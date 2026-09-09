// Lean compiler output
// Module: Init.Meta.Defs
// Imports: import all Init.Prelude public import Init.Data.Array.Basic public import Init.MetaTypes import Init.Data.Array.GetLit import Init.Data.Char.Basic meta import Init.MetaTypes import Init.WFTactics
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_any(lean_object*, lean_object*);
lean_object* lean_substring_drop(lean_object*, lean_object*);
uint8_t lean_substring_all(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_string_contains(lean_object*, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_string_isempty(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprSourceInfo_repr(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
uint32_t lean_substring_front(lean_object*);
uint8_t lean_substring_isempty(lean_object*);
lean_object* lean_substring_takewhile(lean_object*, lean_object*);
lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_pos_min(lean_object*, lean_object*);
lean_object* lean_substring_prev(lean_object*, lean_object*);
uint32_t lean_substring_get(lean_object*, lean_object*);
uint32_t lean_string_front(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(lean_object*);
lean_object* lean_string_drop(lean_object*, lean_object*);
lean_object* lean_string_dropright(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_string_pos_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* lean_nat_pred(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_substring_beq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Char_quote(uint32_t);
lean_object* lean_string_trim(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailing_x3f(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntaxArray_mkImpl___boxed(lean_object*, lean_object*);
lean_object* lean_string_capitalize(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_version_get_major(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_major___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_major___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_major;
lean_object* lean_version_get_minor(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_minor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_minor___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_minor;
lean_object* lean_version_get_patch(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_patch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_patch___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_patch;
lean_object* lean_get_githash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object*);
static lean_once_cell_t l_Lean_githash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_githash___closed__0;
LEAN_EXPORT lean_object* l_Lean_githash;
uint8_t lean_version_get_is_release(lean_object*);
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_isRelease___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_version_isRelease___closed__0;
LEAN_EXPORT uint8_t l_Lean_version_isRelease;
lean_object* lean_version_get_special_desc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object*);
static lean_once_cell_t l_Lean_version_specialDesc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_version_specialDesc___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_specialDesc;
static lean_once_cell_t l_Lean_versionStringCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__0;
static const lean_string_object l_Lean_versionStringCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_versionStringCore___closed__1 = (const lean_object*)&l_Lean_versionStringCore___closed__1_value;
static lean_once_cell_t l_Lean_versionStringCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__2;
static lean_once_cell_t l_Lean_versionStringCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__3;
static lean_once_cell_t l_Lean_versionStringCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__4;
static lean_once_cell_t l_Lean_versionStringCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__5;
static lean_once_cell_t l_Lean_versionStringCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__6;
static lean_once_cell_t l_Lean_versionStringCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionStringCore___closed__7;
LEAN_EXPORT lean_object* l_Lean_versionStringCore;
static const lean_string_object l_Lean_versionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_versionString___closed__0 = (const lean_object*)&l_Lean_versionString___closed__0_value;
static lean_once_cell_t l_Lean_versionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_versionString___closed__1;
static const lean_string_object l_Lean_versionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_versionString___closed__2 = (const lean_object*)&l_Lean_versionString___closed__2_value;
static lean_once_cell_t l_Lean_versionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__3;
static lean_once_cell_t l_Lean_versionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__4;
static const lean_string_object l_Lean_versionString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l_Lean_versionString___closed__5 = (const lean_object*)&l_Lean_versionString___closed__5_value;
static lean_once_cell_t l_Lean_versionString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__6;
static lean_once_cell_t l_Lean_versionString___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versionString___closed__7;
LEAN_EXPORT lean_object* l_Lean_versionString;
static const lean_string_object l_Lean_origin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "leanprover/lean4"};
static const lean_object* l_Lean_origin___closed__0 = (const lean_object*)&l_Lean_origin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_origin = (const lean_object*)&l_Lean_origin___closed__0_value;
static const lean_string_object l_Lean_toolchain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_toolchain___closed__0 = (const lean_object*)&l_Lean_toolchain___closed__0_value;
static lean_once_cell_t l_Lean_toolchain___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__1;
static lean_once_cell_t l_Lean_toolchain___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__2;
static lean_once_cell_t l_Lean_toolchain___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__3;
static lean_once_cell_t l_Lean_toolchain___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__4;
static lean_once_cell_t l_Lean_toolchain___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_toolchain___closed__5;
LEAN_EXPORT lean_object* l_Lean_toolchain;
uint8_t lean_internal_is_stage0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object*);
static lean_once_cell_t l_Lean_isIdFirstAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdFirstAscii___closed__0;
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object*);
static lean_once_cell_t l_Lean_isIdRestAscii___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__0;
static lean_once_cell_t l_Lean_isIdRestAscii___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__1;
static lean_once_cell_t l_Lean_isIdRestAscii___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_isIdRestAscii___closed__2;
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT uint32_t l_Lean_idEndEscape;
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t);
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object*);
static const lean_string_object l_Lean_Name_isInaccessibleUserName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "_inaccessible"};
static const lean_object* l_Lean_Name_isInaccessibleUserName___closed__0 = (const lean_object*)&l_Lean_Name_isInaccessibleUserName___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isIdRest___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_isIdEndEscape___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0_value;
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3_value;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object*);
static const lean_string_object l_Lean_Name_reprPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Name.anonymous"};
static const lean_object* l_Lean_Name_reprPrec___closed__0 = (const lean_object*)&l_Lean_Name_reprPrec___closed__0_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__0_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__1 = (const lean_object*)&l_Lean_Name_reprPrec___closed__1_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Name_reprPrec___closed__2 = (const lean_object*)&l_Lean_Name_reprPrec___closed__2_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__2_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__3 = (const lean_object*)&l_Lean_Name_reprPrec___closed__3_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Name.mkStr "};
static const lean_object* l_Lean_Name_reprPrec___closed__4 = (const lean_object*)&l_Lean_Name_reprPrec___closed__4_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__4_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__5 = (const lean_object*)&l_Lean_Name_reprPrec___closed__5_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Name_reprPrec___closed__6 = (const lean_object*)&l_Lean_Name_reprPrec___closed__6_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__6_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__7 = (const lean_object*)&l_Lean_Name_reprPrec___closed__7_value;
static const lean_string_object l_Lean_Name_reprPrec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Name.mkNum "};
static const lean_object* l_Lean_Name_reprPrec___closed__8 = (const lean_object*)&l_Lean_Name_reprPrec___closed__8_value;
static const lean_ctor_object l_Lean_Name_reprPrec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Name_reprPrec___closed__8_value)}};
static const lean_object* l_Lean_Name_reprPrec___closed__9 = (const lean_object*)&l_Lean_Name_reprPrec___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Name_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Name_instRepr___closed__0 = (const lean_object*)&l_Lean_Name_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Name_instRepr = (const lean_object*)&l_Lean_Name_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_append_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_append_before(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Syntax_instReprPreresolved_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Syntax.Preresolved.namespace"};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__1 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__2 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__2_value;
static lean_once_cell_t l_Lean_Syntax_instReprPreresolved_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__3;
static lean_once_cell_t l_Lean_Syntax_instReprPreresolved_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__4;
static const lean_string_object l_Lean_Syntax_instReprPreresolved_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Syntax.Preresolved.decl"};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__5 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__6 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_instReprPreresolved_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__7 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instReprPreresolved___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instReprPreresolved_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instReprPreresolved___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprPreresolved___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instReprPreresolved = (const lean_object*)&l_Lean_Syntax_instReprPreresolved___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object*);
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Syntax.missing"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__0 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__1 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__1_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Syntax.node"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__2 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__2_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__3 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__3_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__4 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__4_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1;
static lean_once_cell_t l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2;
static const lean_ctor_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Syntax.atom"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__5 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__6 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__7 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__7_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Syntax.ident"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__8 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__8_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__8_value)}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__9 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__9_value;
static const lean_ctor_object l_Lean_Syntax_instRepr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instRepr_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__10 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__10_value;
static const lean_string_object l_Lean_Syntax_instRepr_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ".toRawSubstring"};
static const lean_object* l_Lean_Syntax_instRepr_repr___closed__11 = (const lean_object*)&l_Lean_Syntax_instRepr_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instRepr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instRepr___closed__0 = (const lean_object*)&l_Lean_Syntax_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instRepr = (const lean_object*)&l_Lean_Syntax_instRepr___closed__0_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7;
static const lean_string_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0 = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_TSyntax_instCoeIdentTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_instCoeIdentTerm___closed__0 = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeIdentTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeStrLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNameLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeScientificLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeCharLitTerm = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeIdentLevel = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitPrio = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_TSyntax_instCoeNumLitPrec = (const lean_object*)&l_Lean_TSyntax_instCoeIdentTerm___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instBEqPreresolved___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instBEqPreresolved_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqPreresolved___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqPreresolved___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instBEqPreresolved = (const lean_object*)&l_Lean_Syntax_instBEqPreresolved___closed__0_value;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_structEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEq___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instBEq = (const lean_object*)&l_Lean_Syntax_instBEq___closed__0_value;
static const lean_closure_object l_Lean_Syntax_instBEqTSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_structEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqTSyntax___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqTSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_expandMacros___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__0 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__1 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__2 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value;
static const lean_string_object l_Lean_expandMacros___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_expandMacros___lam__0___closed__3 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_expandMacros___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_expandMacros___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_expandMacros___lam__0___closed__4 = (const lean_object*)&l_Lean_expandMacros___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_expandMacros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_expandMacros___closed__0 = (const lean_object*)&l_Lean_expandMacros___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCIdentFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_internal"};
static const lean_object* l_Lean_mkCIdentFrom___closed__0 = (const lean_object*)&l_Lean_mkCIdentFrom___closed__0_value;
static const lean_ctor_object l_Lean_mkCIdentFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCIdentFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 131, 204, 40, 20, 233, 244, 88)}};
static const lean_object* l_Lean_mkCIdentFrom___closed__1 = (const lean_object*)&l_Lean_mkCIdentFrom___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object*);
static const lean_string_object l_Lean_mkGroupNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_mkGroupNode___closed__0 = (const lean_object*)&l_Lean_mkGroupNode___closed__0_value;
static const lean_ctor_object l_Lean_mkGroupNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkGroupNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_mkGroupNode___closed__1 = (const lean_object*)&l_Lean_mkGroupNode___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_mkSepArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mkSepArray___closed__0 = (const lean_object*)&l_Lean_mkSepArray___closed__0_value;
static const lean_ctor_object l_Lean_mkSepArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSepArray___closed__0_value)}};
static const lean_object* l_Lean_mkSepArray___closed__1 = (const lean_object*)&l_Lean_mkSepArray___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkOptionalNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_mkOptionalNode___closed__0 = (const lean_object*)&l_Lean_mkOptionalNode___closed__0_value;
static const lean_ctor_object l_Lean_mkOptionalNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_mkOptionalNode___closed__1 = (const lean_object*)&l_Lean_mkOptionalNode___closed__1_value;
static const lean_ctor_object l_Lean_mkOptionalNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__1_value),((lean_object*)&l_Lean_mkSepArray___closed__0_value)}};
static const lean_object* l_Lean_mkOptionalNode___closed__2 = (const lean_object*)&l_Lean_mkOptionalNode___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object*);
static const lean_string_object l_Lean_mkHole___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_mkHole___closed__0 = (const lean_object*)&l_Lean_mkHole___closed__0_value;
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_mkHole___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHole___closed__1_value_aux_2),((lean_object*)&l_Lean_mkHole___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_mkHole___closed__1 = (const lean_object*)&l_Lean_mkHole___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_SepArray_ofElems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_SepArray_ofElems___closed__0 = (const lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_SepArray_ofElems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_mkOptionalNode___closed__1_value),((lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__0_value)}};
static const lean_object* l_Lean_Syntax_SepArray_ofElems___closed__1 = (const lean_object*)&l_Lean_Syntax_SepArray_ofElems___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Syntax_mkApp___closed__0 = (const lean_object*)&l_Lean_Syntax_mkApp___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Syntax_mkApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkApp___closed__1_value_aux_2),((lean_object*)&l_Lean_Syntax_mkApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Syntax_mkApp___closed__1 = (const lean_object*)&l_Lean_Syntax_mkApp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkCharLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_Syntax_mkCharLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkCharLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkCharLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkCharLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_Syntax_mkCharLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkCharLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkStrLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Syntax_mkStrLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkStrLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkStrLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkStrLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Syntax_mkStrLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkStrLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkNumLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Syntax_mkNumLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkNumLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkNumLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkNumLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Syntax_mkNumLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkNumLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkScientificLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_Syntax_mkScientificLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkScientificLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkScientificLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkScientificLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_Syntax_mkScientificLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkScientificLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_mkNameLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Syntax_mkNameLit___closed__0 = (const lean_object*)&l_Lean_Syntax_mkNameLit___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkNameLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkNameLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Syntax_mkNameLit___closed__1 = (const lean_object*)&l_Lean_Syntax_mkNameLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Syntax_decodeNatLitVal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_decodeNatLitVal_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_isFieldIdx_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l_Lean_Syntax_isFieldIdx_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_isFieldIdx_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l_Lean_Syntax_isFieldIdx_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_isFieldIdx_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_decodeStringGap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_decodeStringGap___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_decodeStringGap___closed__0 = (const lean_object*)&l_Lean_Syntax_decodeStringGap___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t, uint8_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Init.Meta.Defs"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0_value;
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Substring.Raw.toName"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1_value;
static const lean_string_object l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2 = (const lean_object*)&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2_value;
static lean_once_cell_t l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3;
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object*);
LEAN_EXPORT lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
static const lean_ctor_object l_Lean_TSyntax_getScientific___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_TSyntax_getScientific___closed__0 = (const lean_object*)&l_Lean_TSyntax_getScientific___closed__0_value;
static const lean_ctor_object l_Lean_TSyntax_getScientific___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_getScientific___closed__0_value)}};
static const lean_object* l_Lean_TSyntax_getScientific___closed__1 = (const lean_object*)&l_Lean_TSyntax_getScientific___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instQuoteTermMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instQuoteTermMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteTermMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteTermMkStr1 = (const lean_object*)&l_Lean_instQuoteTermMkStr1___closed__0_value;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__3;
static const lean_string_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__4 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__5 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instQuoteBoolMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteBoolMkStr1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteBoolMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteBoolMkStr1 = (const lean_object*)&l_Lean_instQuoteBoolMkStr1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instQuoteCharCharLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteCharCharLitKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteCharCharLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteCharCharLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteCharCharLitKind = (const lean_object*)&l_Lean_instQuoteCharCharLitKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteStringStrLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteStringStrLitKind___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteStringStrLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteStringStrLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteStringStrLitKind = (const lean_object*)&l_Lean_instQuoteStringStrLitKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteNatNumLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteNatNumLitKind___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteNatNumLitKind___closed__0 = (const lean_object*)&l_Lean_instQuoteNatNumLitKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteNatNumLitKind = (const lean_object*)&l_Lean_instQuoteNatNumLitKind___closed__0_value;
static const lean_string_object l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toRawSubstring'"};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 31, 121, 163, 121, 213, 247, 150)}};
static const lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteRawMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteRawMkStr1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteRawMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteRawMkStr1 = (const lean_object*)&l_Lean_instQuoteRawMkStr1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static const lean_string_object l_Lean_quoteNameMk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l_Lean_quoteNameMk___closed__0 = (const lean_object*)&l_Lean_quoteNameMk___closed__0_value;
static const lean_string_object l_Lean_quoteNameMk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "anonymous"};
static const lean_object* l_Lean_quoteNameMk___closed__1 = (const lean_object*)&l_Lean_quoteNameMk___closed__1_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__2_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__2_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 163, 3, 148, 15, 163, 84, 121)}};
static const lean_object* l_Lean_quoteNameMk___closed__2 = (const lean_object*)&l_Lean_quoteNameMk___closed__2_value;
static lean_once_cell_t l_Lean_quoteNameMk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_quoteNameMk___closed__3;
static const lean_string_object l_Lean_quoteNameMk___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkStr"};
static const lean_object* l_Lean_quoteNameMk___closed__4 = (const lean_object*)&l_Lean_quoteNameMk___closed__4_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__5_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__5_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 239, 13, 154, 0, 241, 98, 75)}};
static const lean_object* l_Lean_quoteNameMk___closed__5 = (const lean_object*)&l_Lean_quoteNameMk___closed__5_value;
static const lean_string_object l_Lean_quoteNameMk___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkNum"};
static const lean_object* l_Lean_quoteNameMk___closed__6 = (const lean_object*)&l_Lean_quoteNameMk___closed__6_value;
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__7_value_aux_0),((lean_object*)&l_Lean_quoteNameMk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l_Lean_quoteNameMk___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_quoteNameMk___closed__7_value_aux_1),((lean_object*)&l_Lean_quoteNameMk___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 141, 7, 17, 149, 107, 178, 15)}};
static const lean_object* l_Lean_quoteNameMk___closed__7 = (const lean_object*)&l_Lean_quoteNameMk___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object*);
static const lean_string_object l_Lean_instQuoteNameMkStr1___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_instQuoteNameMkStr1___private__1___closed__0 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__0_value;
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_instQuoteNameMkStr1___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value_aux_2),((lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_instQuoteNameMkStr1___private__1___closed__1 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___private__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object*);
static const lean_closure_object l_Lean_instQuoteNameMkStr1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instQuoteNameMkStr1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instQuoteNameMkStr1___closed__0 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instQuoteNameMkStr1 = (const lean_object*)&l_Lean_instQuoteNameMkStr1___closed__0_value;
static const lean_string_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0_value;
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkArray"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1 = (const lean_object*)&l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__3;
static const lean_string_object l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_evalPrec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected precedence"};
static const lean_object* l_Lean_evalPrec___closed__0 = (const lean_object*)&l_Lean_evalPrec___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_evalPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unexpected priority"};
static const lean_object* l_Lean_evalPrio___closed__0 = (const lean_object*)&l_Lean_evalPrio___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_getSepElems___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_getSepElems___redArg___closed__0 = (const lean_object*)&l_Array_getSepElems___redArg___closed__0_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__1 = (const lean_object*)&l_Array_getSepElems___redArg___closed__1_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__2 = (const lean_object*)&l_Array_getSepElems___redArg___closed__2_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__3 = (const lean_object*)&l_Array_getSepElems___redArg___closed__3_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__4 = (const lean_object*)&l_Array_getSepElems___redArg___closed__4_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__5 = (const lean_object*)&l_Array_getSepElems___redArg___closed__5_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__6 = (const lean_object*)&l_Array_getSepElems___redArg___closed__6_value;
static const lean_closure_object l_Array_getSepElems___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_getSepElems___redArg___closed__7 = (const lean_object*)&l_Array_getSepElems___redArg___closed__7_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__1_value),((lean_object*)&l_Array_getSepElems___redArg___closed__2_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__8 = (const lean_object*)&l_Array_getSepElems___redArg___closed__8_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__8_value),((lean_object*)&l_Array_getSepElems___redArg___closed__3_value),((lean_object*)&l_Array_getSepElems___redArg___closed__4_value),((lean_object*)&l_Array_getSepElems___redArg___closed__5_value),((lean_object*)&l_Array_getSepElems___redArg___closed__6_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__9 = (const lean_object*)&l_Array_getSepElems___redArg___closed__9_value;
static const lean_ctor_object l_Array_getSepElems___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_getSepElems___redArg___closed__9_value),((lean_object*)&l_Array_getSepElems___redArg___closed__7_value)}};
static const lean_object* l_Array_getSepElems___redArg___closed__10 = (const lean_object*)&l_Array_getSepElems___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeOutTSepArraySepArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeOutTSepArraySepArray___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeOutTSepArraySepArray___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value;
static const lean_string_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0 = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object*);
static const lean_string_object l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "interpolatedStrLitKind"};
static const lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 181, 130, 246, 88, 58, 26, 43)}};
static const lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_TSyntax_expandInterpolatedStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__0 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__0_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__1 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__1_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value_aux_2),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__2 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__2_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__3 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__3_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_1),((lean_object*)&l_Lean_expandMacros___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value_aux_2),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__4 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__4_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__5 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__5_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__6 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__6_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__7 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__7_value;
static lean_once_cell_t l_Lean_TSyntax_expandInterpolatedStr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__8;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "TSyntax"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__9 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value_aux_0),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(208, 86, 51, 178, 37, 75, 0, 6)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__10 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__10_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__11 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__11_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Compat"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__12 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__12_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_0),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(208, 86, 51, 178, 37, 75, 0, 6)}};
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value_aux_1),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(233, 134, 124, 217, 96, 118, 79, 86)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__13 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__13_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__14 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__14_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__15 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__15_value;
static const lean_ctor_object l_Lean_TSyntax_expandInterpolatedStr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__11_value),((lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__15_value)}};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__16 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__16_value;
static const lean_string_object l_Lean_TSyntax_expandInterpolatedStr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__17 = (const lean_object*)&l_Lean_TSyntax_expandInterpolatedStr___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.TransparencyMode.all"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.TransparencyMode.default"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.TransparencyMode.reducible"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.TransparencyMode.instances"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__6 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__7 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.TransparencyMode.none"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__8 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__9 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__9_value;
static const lean_string_object l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.TransparencyMode.implicit"};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__10 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_instReprTransparencyMode_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__10_value)}};
static const lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__11 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprTransparencyMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprTransparencyMode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprTransparencyMode___closed__0 = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprTransparencyMode = (const lean_object*)&l_Lean_Meta_instReprTransparencyMode___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.EtaStructMode.all"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.EtaStructMode.notClasses"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.EtaStructMode.none"};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprEtaStructMode_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprEtaStructMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprEtaStructMode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprEtaStructMode___closed__0 = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprEtaStructMode = (const lean_object*)&l_Lean_Meta_instReprEtaStructMode___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "etaStruct"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iota"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__18;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "autoUnfold"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__19_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__20_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__21;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "failIfUnchanged"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__22_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__23_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__24;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unfoldPartialApp"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__25 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__25_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__26_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__27;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "zetaDelta"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__29_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "index"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__30 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__30_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__31_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__32;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "zetaUnused"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__33_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__34_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "zetaHave"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__35 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__35_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__36_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__37;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "locals"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__38_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__39_value;
static const lean_string_object l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__40 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__40_value)}};
static const lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__41 = (const lean_object*)&l_Lean_Meta_instReprConfig_repr___redArg___closed__41_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprConfig_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprConfig___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprConfig = (const lean_object*)&l_Lean_Meta_instReprConfig___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Option_hasQuote___redArg___lam__0___closed__1_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__1_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxSteps"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "maxDischargeDepth"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "contextual"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "memoize"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "singlePass"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dsimp"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ground"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "implicitDefEqProofs"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "catchRuntime"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "congrConsts"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bitVecOfNat"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "warnExponents"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggestions"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37_value;
static const lean_string_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "maxSuggestions"};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__38_value)}};
static const lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39_value;
static lean_once_cell_t l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprConfig__1_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprConfig__1___closed__0 = (const lean_object*)&l_Lean_Meta_instReprConfig__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprConfig__1 = (const lean_object*)&l_Lean_Meta_instReprConfig__1___closed__0_value;
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__1_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_getConfigItems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_expandMacros___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_0),((lean_object*)&l_Lean_expandMacros___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_getConfigItems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 254, 59, 95, 54, 234, 162, 220)}};
static const lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_getConfigItems___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object* v_u_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_version_get_major(v_u_2_);
return v_res_3_;
}
}
static lean_object* _init_l_Lean_version_major___closed__0(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_version_get_major(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_version_major(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_obj_once(&l_Lean_version_major___closed__0, &l_Lean_version_major___closed__0_once, _init_l_Lean_version_major___closed__0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object* v_u_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_version_get_minor(v_u_8_);
return v_res_9_;
}
}
static lean_object* _init_l_Lean_version_minor___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(0);
v___x_11_ = lean_version_get_minor(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_version_minor(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_version_minor___closed__0, &l_Lean_version_minor___closed__0_once, _init_l_Lean_version_minor___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object* v_u_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lean_version_get_patch(v_u_14_);
return v_res_15_;
}
}
static lean_object* _init_l_Lean_version_patch___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_box(0);
v___x_17_ = lean_version_get_patch(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_version_patch(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_version_patch___closed__0, &l_Lean_version_patch___closed__0_once, _init_l_Lean_version_patch___closed__0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object* v_u_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_get_githash(v_u_20_);
return v_res_21_;
}
}
static lean_object* _init_l_Lean_githash___closed__0(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_get_githash(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_githash(void){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_githash___closed__0, &l_Lean_githash___closed__0_once, _init_l_Lean_githash___closed__0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object* v_u_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = lean_version_get_is_release(v_u_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
static uint8_t _init_l_Lean_version_isRelease___closed__0(void){
_start:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_version_get_is_release(v___x_29_);
return v___x_30_;
}
}
static uint8_t _init_l_Lean_version_isRelease(void){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_uint8_once(&l_Lean_version_isRelease___closed__0, &l_Lean_version_isRelease___closed__0_once, _init_l_Lean_version_isRelease___closed__0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object* v_u_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lean_version_get_special_desc(v_u_33_);
return v_res_34_;
}
}
static lean_object* _init_l_Lean_version_specialDesc___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_box(0);
v___x_36_ = lean_version_get_special_desc(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_version_specialDesc(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l_Lean_version_specialDesc___closed__0, &l_Lean_version_specialDesc___closed__0_once, _init_l_Lean_version_specialDesc___closed__0);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = l_Lean_version_major;
v___x_39_ = l_Nat_reprFast(v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_42_ = lean_obj_once(&l_Lean_versionStringCore___closed__0, &l_Lean_versionStringCore___closed__0_once, _init_l_Lean_versionStringCore___closed__0);
v___x_43_ = lean_string_append(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__3(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = l_Lean_version_minor;
v___x_45_ = l_Nat_reprFast(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__4(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&l_Lean_versionStringCore___closed__3, &l_Lean_versionStringCore___closed__3_once, _init_l_Lean_versionStringCore___closed__3);
v___x_47_ = lean_obj_once(&l_Lean_versionStringCore___closed__2, &l_Lean_versionStringCore___closed__2_once, _init_l_Lean_versionStringCore___closed__2);
v___x_48_ = lean_string_append(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__5(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_50_ = lean_obj_once(&l_Lean_versionStringCore___closed__4, &l_Lean_versionStringCore___closed__4_once, _init_l_Lean_versionStringCore___closed__4);
v___x_51_ = lean_string_append(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__6(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = l_Lean_version_patch;
v___x_53_ = l_Nat_reprFast(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__7(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_versionStringCore___closed__6, &l_Lean_versionStringCore___closed__6_once, _init_l_Lean_versionStringCore___closed__6);
v___x_55_ = lean_obj_once(&l_Lean_versionStringCore___closed__5, &l_Lean_versionStringCore___closed__5_once, _init_l_Lean_versionStringCore___closed__5);
v___x_56_ = lean_string_append(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_versionStringCore(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_Lean_versionStringCore___closed__7, &l_Lean_versionStringCore___closed__7_once, _init_l_Lean_versionStringCore___closed__7);
return v___x_57_;
}
}
static uint8_t _init_l_Lean_versionString___closed__1(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_59_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_60_ = l_Lean_version_specialDesc;
v___x_61_ = lean_string_dec_eq(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_versionString___closed__3(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_64_ = l_Lean_versionStringCore;
v___x_65_ = lean_string_append(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_versionString___closed__4(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = l_Lean_version_specialDesc;
v___x_67_ = lean_obj_once(&l_Lean_versionString___closed__3, &l_Lean_versionString___closed__3_once, _init_l_Lean_versionString___closed__3);
v___x_68_ = lean_string_append(v___x_67_, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_versionString___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = ((lean_object*)(l_Lean_versionString___closed__5));
v___x_71_ = l_Lean_versionStringCore;
v___x_72_ = lean_string_append(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_versionString___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = l_Lean_githash;
v___x_74_ = lean_obj_once(&l_Lean_versionString___closed__6, &l_Lean_versionString___closed__6_once, _init_l_Lean_versionString___closed__6);
v___x_75_ = lean_string_append(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_versionString(void){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_versionString___closed__4, &l_Lean_versionString___closed__4_once, _init_l_Lean_versionString___closed__4);
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = l_Lean_version_isRelease;
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_versionString___closed__7, &l_Lean_versionString___closed__7_once, _init_l_Lean_versionString___closed__7);
return v___x_79_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_versionStringCore;
return v___x_80_;
}
}
}
}
static lean_object* _init_l_Lean_toolchain___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_85_ = ((lean_object*)(l_Lean_origin___closed__0));
v___x_86_ = lean_string_append(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__2(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = l_Lean_version_specialDesc;
v___x_88_ = lean_obj_once(&l_Lean_toolchain___closed__1, &l_Lean_toolchain___closed__1_once, _init_l_Lean_toolchain___closed__1);
v___x_89_ = lean_string_append(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__3(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = l_Lean_versionStringCore;
v___x_91_ = lean_obj_once(&l_Lean_toolchain___closed__1, &l_Lean_toolchain___closed__1_once, _init_l_Lean_toolchain___closed__1);
v___x_92_ = lean_string_append(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__4(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((lean_object*)(l_Lean_versionString___closed__2));
v___x_94_ = lean_obj_once(&l_Lean_toolchain___closed__3, &l_Lean_toolchain___closed__3_once, _init_l_Lean_toolchain___closed__3);
v___x_95_ = lean_string_append(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_toolchain___closed__5(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = l_Lean_version_specialDesc;
v___x_97_ = lean_obj_once(&l_Lean_toolchain___closed__4, &l_Lean_toolchain___closed__4_once, _init_l_Lean_toolchain___closed__4);
v___x_98_ = lean_string_append(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_toolchain(void){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_100_ = lean_uint8_once(&l_Lean_versionString___closed__1, &l_Lean_versionString___closed__1_once, _init_l_Lean_versionString___closed__1);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; 
v___x_101_ = l_Lean_version_isRelease;
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_toolchain___closed__2, &l_Lean_toolchain___closed__2_once, _init_l_Lean_toolchain___closed__2);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_toolchain___closed__5, &l_Lean_toolchain___closed__5_once, _init_l_Lean_toolchain___closed__5);
return v___x_103_;
}
}
else
{
uint8_t v___x_104_; 
v___x_104_ = l_Lean_version_isRelease;
if (v___x_104_ == 0)
{
return v___x_99_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_toolchain___closed__3, &l_Lean_toolchain___closed__3_once, _init_l_Lean_toolchain___closed__3);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object* v_u_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = lean_internal_is_stage0(v_u_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object* v_u_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = lean_internal_has_llvm_backend(v_u_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t v_c_114_){
_start:
{
uint32_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 913;
v___x_116_ = lean_uint32_dec_le(v___x_115_, v_c_114_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 989;
v___x_118_ = lean_uint32_dec_le(v_c_114_, v___x_117_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object* v_c_119_){
_start:
{
uint32_t v_c_boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v_c_boxed_120_ = lean_unbox_uint32(v_c_119_);
lean_dec(v_c_119_);
v_res_121_ = l_Lean_isGreek(v_c_boxed_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t v_c_123_){
_start:
{
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 945;
v___x_168_ = lean_uint32_dec_le(v___x_167_, v_c_123_);
if (v___x_168_ == 0)
{
goto v___jp_158_;
}
else
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 969;
v___x_170_ = lean_uint32_dec_le(v_c_123_, v___x_169_);
if (v___x_170_ == 0)
{
goto v___jp_158_;
}
else
{
uint32_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 955;
v___x_172_ = lean_uint32_dec_eq(v_c_123_, v___x_171_);
if (v___x_172_ == 0)
{
if (v___x_170_ == 0)
{
goto v___jp_158_;
}
else
{
return v___x_170_;
}
}
else
{
goto v___jp_158_;
}
}
}
v___jp_124_:
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 256;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v_c_123_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 383;
v___x_128_ = lean_uint32_dec_le(v_c_123_, v___x_127_);
return v___x_128_;
}
}
v___jp_129_:
{
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 192;
v___x_131_ = lean_uint32_dec_le(v___x_130_, v_c_123_);
if (v___x_131_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 255;
v___x_133_ = lean_uint32_dec_le(v_c_123_, v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 215;
v___x_135_ = lean_uint32_dec_eq(v_c_123_, v___x_134_);
if (v___x_135_ == 0)
{
if (v___x_133_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 247;
v___x_137_ = lean_uint32_dec_eq(v_c_123_, v___x_136_);
if (v___x_137_ == 0)
{
return v___x_133_;
}
else
{
goto v___jp_124_;
}
}
}
else
{
goto v___jp_124_;
}
}
}
}
v___jp_138_:
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 119964;
v___x_140_ = lean_uint32_dec_le(v___x_139_, v_c_123_);
if (v___x_140_ == 0)
{
goto v___jp_129_;
}
else
{
uint32_t v___x_141_; uint8_t v___x_142_; 
v___x_141_ = 120223;
v___x_142_ = lean_uint32_dec_le(v_c_123_, v___x_141_);
if (v___x_142_ == 0)
{
goto v___jp_129_;
}
else
{
return v___x_142_;
}
}
}
v___jp_143_:
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 8448;
v___x_145_ = lean_uint32_dec_le(v___x_144_, v_c_123_);
if (v___x_145_ == 0)
{
goto v___jp_138_;
}
else
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 8527;
v___x_147_ = lean_uint32_dec_le(v_c_123_, v___x_146_);
if (v___x_147_ == 0)
{
goto v___jp_138_;
}
else
{
return v___x_147_;
}
}
}
v___jp_148_:
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 7936;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v_c_123_);
if (v___x_150_ == 0)
{
goto v___jp_143_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 8190;
v___x_152_ = lean_uint32_dec_le(v_c_123_, v___x_151_);
if (v___x_152_ == 0)
{
goto v___jp_143_;
}
else
{
return v___x_152_;
}
}
}
v___jp_153_:
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 970;
v___x_155_ = lean_uint32_dec_le(v___x_154_, v_c_123_);
if (v___x_155_ == 0)
{
goto v___jp_148_;
}
else
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 1019;
v___x_157_ = lean_uint32_dec_le(v_c_123_, v___x_156_);
if (v___x_157_ == 0)
{
goto v___jp_148_;
}
else
{
return v___x_157_;
}
}
}
v___jp_158_:
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 913;
v___x_160_ = lean_uint32_dec_le(v___x_159_, v_c_123_);
if (v___x_160_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_161_ = 937;
v___x_162_ = lean_uint32_dec_le(v_c_123_, v___x_161_);
if (v___x_162_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = 928;
v___x_164_ = lean_uint32_dec_eq(v_c_123_, v___x_163_);
if (v___x_164_ == 0)
{
if (v___x_162_ == 0)
{
goto v___jp_153_;
}
else
{
uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_165_ = 931;
v___x_166_ = lean_uint32_dec_eq(v_c_123_, v___x_165_);
if (v___x_166_ == 0)
{
return v___x_162_;
}
else
{
goto v___jp_153_;
}
}
}
else
{
goto v___jp_153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object* v_c_173_){
_start:
{
uint32_t v_c_boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_c_boxed_174_ = lean_unbox_uint32(v_c_173_);
lean_dec(v_c_173_);
v_res_175_ = l_Lean_isLetterLike(v_c_boxed_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t v_c_177_){
_start:
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 8320;
v___x_179_ = lean_uint32_dec_le(v___x_178_, v_c_177_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 8329;
v___x_181_ = lean_uint32_dec_le(v_c_177_, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object* v_c_182_){
_start:
{
uint32_t v_c_boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v_c_boxed_183_ = lean_unbox_uint32(v_c_182_);
lean_dec(v_c_182_);
v_res_184_ = l_Lean_isNumericSubscript(v_c_boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t v_c_186_){
_start:
{
uint32_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 8320;
v___x_201_ = lean_uint32_dec_le(v___x_200_, v_c_186_);
if (v___x_201_ == 0)
{
goto v___jp_195_;
}
else
{
uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 8329;
v___x_203_ = lean_uint32_dec_le(v_c_186_, v___x_202_);
if (v___x_203_ == 0)
{
goto v___jp_195_;
}
else
{
return v___x_203_;
}
}
v___jp_187_:
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 11388;
v___x_189_ = lean_uint32_dec_eq(v_c_186_, v___x_188_);
return v___x_189_;
}
v___jp_190_:
{
uint32_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = 7522;
v___x_192_ = lean_uint32_dec_le(v___x_191_, v_c_186_);
if (v___x_192_ == 0)
{
goto v___jp_187_;
}
else
{
uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = 7530;
v___x_194_ = lean_uint32_dec_le(v_c_186_, v___x_193_);
if (v___x_194_ == 0)
{
goto v___jp_187_;
}
else
{
return v___x_194_;
}
}
}
v___jp_195_:
{
uint32_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = 8336;
v___x_197_ = lean_uint32_dec_le(v___x_196_, v_c_186_);
if (v___x_197_ == 0)
{
goto v___jp_190_;
}
else
{
uint32_t v___x_198_; uint8_t v___x_199_; 
v___x_198_ = 8348;
v___x_199_ = lean_uint32_dec_le(v_c_186_, v___x_198_);
if (v___x_199_ == 0)
{
goto v___jp_190_;
}
else
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* v_c_204_){
_start:
{
uint32_t v_c_boxed_205_; uint8_t v_res_206_; lean_object* v_r_207_; 
v_c_boxed_205_ = lean_unbox_uint32(v_c_204_);
lean_dec(v_c_204_);
v_res_206_ = l_Lean_isSubScriptAlnum(v_c_boxed_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t v_c_208_){
_start:
{
uint8_t v___y_214_; uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 65;
v___x_220_ = lean_uint32_dec_le(v___x_219_, v_c_208_);
if (v___x_220_ == 0)
{
v___y_214_ = v___x_220_;
goto v___jp_213_;
}
else
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 90;
v___x_222_ = lean_uint32_dec_le(v_c_208_, v___x_221_);
v___y_214_ = v___x_222_;
goto v___jp_213_;
}
v___jp_209_:
{
uint32_t v___x_210_; uint8_t v___x_211_; 
v___x_210_ = 95;
v___x_211_ = lean_uint32_dec_eq(v_c_208_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_isLetterLike(v_c_208_);
return v___x_212_;
}
else
{
return v___x_211_;
}
}
v___jp_213_:
{
if (v___y_214_ == 0)
{
uint32_t v___x_215_; uint8_t v___x_216_; 
v___x_215_ = 97;
v___x_216_ = lean_uint32_dec_le(v___x_215_, v_c_208_);
if (v___x_216_ == 0)
{
goto v___jp_209_;
}
else
{
uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = 122;
v___x_218_ = lean_uint32_dec_le(v_c_208_, v___x_217_);
if (v___x_218_ == 0)
{
goto v___jp_209_;
}
else
{
return v___x_218_;
}
}
}
else
{
return v___y_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* v_c_223_){
_start:
{
uint32_t v_c_boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v_c_boxed_224_ = lean_unbox_uint32(v_c_223_);
lean_dec(v_c_223_);
v_res_225_ = l_Lean_isIdFirst(v_c_boxed_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0(void){
_start:
{
uint32_t v___x_227_; uint8_t v___x_228_; 
v___x_227_ = 65;
v___x_228_ = lean_uint32_to_uint8(v___x_227_);
return v___x_228_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1(void){
_start:
{
uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 90;
v___x_230_ = lean_uint32_to_uint8(v___x_229_);
return v___x_230_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2(void){
_start:
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 97;
v___x_232_ = lean_uint32_to_uint8(v___x_231_);
return v___x_232_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3(void){
_start:
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 122;
v___x_234_ = lean_uint32_to_uint8(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t v_c_235_){
_start:
{
uint8_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_242_ = lean_uint8_dec_le(v___x_241_, v_c_235_);
if (v___x_242_ == 0)
{
goto v___jp_236_;
}
else
{
uint8_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_244_ = lean_uint8_dec_le(v_c_235_, v___x_243_);
if (v___x_244_ == 0)
{
goto v___jp_236_;
}
else
{
return v___x_244_;
}
}
v___jp_236_:
{
uint8_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_238_ = lean_uint8_dec_le(v___x_237_, v_c_235_);
if (v___x_238_ == 0)
{
return v___x_238_;
}
else
{
uint8_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_240_ = lean_uint8_dec_le(v_c_235_, v___x_239_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* v_c_245_){
_start:
{
uint8_t v_c_boxed_246_; uint8_t v_res_247_; lean_object* v_r_248_; 
v_c_boxed_246_ = lean_unbox(v_c_245_);
v_res_247_ = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(v_c_boxed_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
static uint8_t _init_l_Lean_isIdFirstAscii___closed__0(void){
_start:
{
uint32_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 95;
v___x_250_ = lean_uint32_to_uint8(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t v_c_251_){
_start:
{
uint8_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_261_ = lean_uint8_dec_le(v___x_260_, v_c_251_);
if (v___x_261_ == 0)
{
goto v___jp_255_;
}
else
{
uint8_t v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_263_ = lean_uint8_dec_le(v_c_251_, v___x_262_);
if (v___x_263_ == 0)
{
goto v___jp_255_;
}
else
{
return v___x_263_;
}
}
v___jp_252_:
{
uint8_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_254_ = lean_uint8_dec_eq(v_c_251_, v___x_253_);
return v___x_254_;
}
v___jp_255_:
{
uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_257_ = lean_uint8_dec_le(v___x_256_, v_c_251_);
if (v___x_257_ == 0)
{
goto v___jp_252_;
}
else
{
uint8_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_259_ = lean_uint8_dec_le(v_c_251_, v___x_258_);
if (v___x_259_ == 0)
{
goto v___jp_252_;
}
else
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* v_c_264_){
_start:
{
uint8_t v_c_boxed_265_; uint8_t v_res_266_; lean_object* v_r_267_; 
v_c_boxed_265_ = lean_unbox(v_c_264_);
v_res_266_ = l_Lean_isIdFirstAscii(v_c_boxed_265_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0(void){
_start:
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 48;
v___x_269_ = lean_uint32_to_uint8(v___x_268_);
return v___x_269_;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1(void){
_start:
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 57;
v___x_271_ = lean_uint32_to_uint8(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t v_c_272_){
_start:
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_284_ = lean_uint8_dec_le(v___x_283_, v_c_272_);
if (v___x_284_ == 0)
{
goto v___jp_278_;
}
else
{
uint8_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_286_ = lean_uint8_dec_le(v_c_272_, v___x_285_);
if (v___x_286_ == 0)
{
goto v___jp_278_;
}
else
{
return v___x_286_;
}
}
v___jp_273_:
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_275_ = lean_uint8_dec_le(v___x_274_, v_c_272_);
if (v___x_275_ == 0)
{
return v___x_275_;
}
else
{
uint8_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_277_ = lean_uint8_dec_le(v_c_272_, v___x_276_);
return v___x_277_;
}
}
v___jp_278_:
{
uint8_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_280_ = lean_uint8_dec_le(v___x_279_, v_c_272_);
if (v___x_280_ == 0)
{
goto v___jp_273_;
}
else
{
uint8_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_282_ = lean_uint8_dec_le(v_c_272_, v___x_281_);
if (v___x_282_ == 0)
{
goto v___jp_273_;
}
else
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* v_c_287_){
_start:
{
uint8_t v_c_boxed_288_; uint8_t v_res_289_; lean_object* v_r_290_; 
v_c_boxed_288_ = lean_unbox(v_c_287_);
v_res_289_ = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(v_c_boxed_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t v_c_291_){
_start:
{
uint8_t v___y_309_; uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 65;
v___x_315_ = lean_uint32_dec_le(v___x_314_, v_c_291_);
if (v___x_315_ == 0)
{
v___y_309_ = v___x_315_;
goto v___jp_308_;
}
else
{
uint32_t v___x_316_; uint8_t v___x_317_; 
v___x_316_ = 90;
v___x_317_ = lean_uint32_dec_le(v_c_291_, v___x_316_);
v___y_309_ = v___x_317_;
goto v___jp_308_;
}
v___jp_292_:
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 95;
v___x_294_ = lean_uint32_dec_eq(v_c_291_, v___x_293_);
if (v___x_294_ == 0)
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 39;
v___x_296_ = lean_uint32_dec_eq(v_c_291_, v___x_295_);
if (v___x_296_ == 0)
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 33;
v___x_298_ = lean_uint32_dec_eq(v_c_291_, v___x_297_);
if (v___x_298_ == 0)
{
uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 63;
v___x_300_ = lean_uint32_dec_eq(v_c_291_, v___x_299_);
if (v___x_300_ == 0)
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_isLetterLike(v_c_291_);
if (v___x_301_ == 0)
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_isSubScriptAlnum(v_c_291_);
return v___x_302_;
}
else
{
return v___x_301_;
}
}
else
{
return v___x_300_;
}
}
else
{
return v___x_298_;
}
}
else
{
return v___x_296_;
}
}
else
{
return v___x_294_;
}
}
v___jp_303_:
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 48;
v___x_305_ = lean_uint32_dec_le(v___x_304_, v_c_291_);
if (v___x_305_ == 0)
{
goto v___jp_292_;
}
else
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 57;
v___x_307_ = lean_uint32_dec_le(v_c_291_, v___x_306_);
if (v___x_307_ == 0)
{
goto v___jp_292_;
}
else
{
return v___x_307_;
}
}
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 97;
v___x_311_ = lean_uint32_dec_le(v___x_310_, v_c_291_);
if (v___x_311_ == 0)
{
goto v___jp_303_;
}
else
{
uint32_t v___x_312_; uint8_t v___x_313_; 
v___x_312_ = 122;
v___x_313_ = lean_uint32_dec_le(v_c_291_, v___x_312_);
if (v___x_313_ == 0)
{
goto v___jp_303_;
}
else
{
return v___x_313_;
}
}
}
else
{
return v___y_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* v_c_318_){
_start:
{
uint32_t v_c_boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_c_boxed_319_ = lean_unbox_uint32(v_c_318_);
lean_dec(v_c_318_);
v_res_320_ = l_Lean_isIdRest(v_c_boxed_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__0(void){
_start:
{
uint32_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 39;
v___x_323_ = lean_uint32_to_uint8(v___x_322_);
return v___x_323_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__1(void){
_start:
{
uint32_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 33;
v___x_325_ = lean_uint32_to_uint8(v___x_324_);
return v___x_325_;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__2(void){
_start:
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 63;
v___x_327_ = lean_uint32_to_uint8(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t v_c_328_){
_start:
{
uint8_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_349_ = lean_uint8_dec_le(v___x_348_, v_c_328_);
if (v___x_349_ == 0)
{
goto v___jp_343_;
}
else
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_351_ = lean_uint8_dec_le(v_c_328_, v___x_350_);
if (v___x_351_ == 0)
{
goto v___jp_343_;
}
else
{
return v___x_351_;
}
}
v___jp_329_:
{
uint8_t v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_331_ = lean_uint8_dec_eq(v_c_328_, v___x_330_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_333_ = lean_uint8_dec_eq(v_c_328_, v___x_332_);
if (v___x_333_ == 0)
{
uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_335_ = lean_uint8_dec_eq(v_c_328_, v___x_334_);
if (v___x_335_ == 0)
{
uint8_t v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_337_ = lean_uint8_dec_eq(v_c_328_, v___x_336_);
return v___x_337_;
}
else
{
return v___x_335_;
}
}
else
{
return v___x_333_;
}
}
else
{
return v___x_331_;
}
}
v___jp_338_:
{
uint8_t v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_340_ = lean_uint8_dec_le(v___x_339_, v_c_328_);
if (v___x_340_ == 0)
{
goto v___jp_329_;
}
else
{
uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_342_ = lean_uint8_dec_le(v_c_328_, v___x_341_);
if (v___x_342_ == 0)
{
goto v___jp_329_;
}
else
{
return v___x_342_;
}
}
}
v___jp_343_:
{
uint8_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_345_ = lean_uint8_dec_le(v___x_344_, v_c_328_);
if (v___x_345_ == 0)
{
goto v___jp_338_;
}
else
{
uint8_t v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_347_ = lean_uint8_dec_le(v_c_328_, v___x_346_);
if (v___x_347_ == 0)
{
goto v___jp_338_;
}
else
{
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* v_c_352_){
_start:
{
uint8_t v_c_boxed_353_; uint8_t v_res_354_; lean_object* v_r_355_; 
v_c_boxed_353_ = lean_unbox(v_c_352_);
v_res_354_ = l_Lean_isIdRestAscii(v_c_boxed_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
static uint32_t _init_l_Lean_idBeginEscape(void){
_start:
{
uint32_t v___x_356_; 
v___x_356_ = 171;
return v___x_356_;
}
}
static uint32_t _init_l_Lean_idEndEscape(void){
_start:
{
uint32_t v___x_357_; 
v___x_357_ = 187;
return v___x_357_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t v_c_358_){
_start:
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 171;
v___x_360_ = lean_uint32_dec_eq(v_c_358_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* v_c_361_){
_start:
{
uint32_t v_c_boxed_362_; uint8_t v_res_363_; lean_object* v_r_364_; 
v_c_boxed_362_ = lean_unbox_uint32(v_c_361_);
lean_dec(v_c_361_);
v_res_363_ = l_Lean_isIdBeginEscape(v_c_boxed_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t v_c_365_){
_start:
{
uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 187;
v___x_367_ = lean_uint32_dec_eq(v_c_365_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* v_c_368_){
_start:
{
uint32_t v_c_boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_c_boxed_369_ = lean_unbox_uint32(v_c_368_);
lean_dec(v_c_368_);
v_res_370_ = l_Lean_isIdEndEscape(v_c_boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
return v_x_372_;
}
else
{
lean_object* v_pre_373_; 
v_pre_373_ = lean_ctor_get(v_x_372_, 0);
if (lean_obj_tag(v_pre_373_) == 0)
{
lean_inc(v_x_372_);
return v_x_372_;
}
else
{
v_x_372_ = v_pre_373_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* v_x_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Name_getRoot(v_x_375_);
lean_dec(v_x_375_);
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Name_isInaccessibleUserName(lean_object* v_x_378_){
_start:
{
switch(lean_obj_tag(v_x_378_))
{
case 1:
{
lean_object* v_str_379_; uint32_t v___x_380_; uint8_t v___x_381_; 
v_str_379_ = lean_ctor_get(v_x_378_, 1);
lean_inc_ref_n(v_str_379_, 2);
lean_dec_ref_known(v_x_378_, 2);
v___x_380_ = 10013;
v___x_381_ = lean_string_contains(v_str_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_Name_isInaccessibleUserName___closed__0));
v___x_383_ = lean_string_dec_eq(v_str_379_, v___x_382_);
lean_dec_ref(v_str_379_);
return v___x_383_;
}
else
{
lean_dec_ref(v_str_379_);
return v___x_381_;
}
}
case 2:
{
lean_object* v_pre_384_; 
v_pre_384_ = lean_ctor_get(v_x_378_, 0);
lean_inc(v_pre_384_);
lean_dec_ref_known(v_x_378_, 2);
v_x_378_ = v_pre_384_;
goto _start;
}
default: 
{
uint8_t v___x_386_; 
lean_dec(v_x_378_);
v___x_386_ = 0;
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* v_x_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_Name_isInaccessibleUserName(v_x_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* v_s_390_, lean_object* v_i_391_){
_start:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_string_utf8_byte_size(v_s_390_);
v___x_397_ = lean_nat_dec_lt(v_i_391_, v___x_396_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; 
lean_dec(v_i_391_);
v___x_398_ = 1;
return v___x_398_;
}
else
{
uint8_t v_c_399_; uint8_t v___x_419_; uint8_t v___x_420_; 
lean_inc(v_i_391_);
v_c_399_ = lean_string_get_byte_fast(v_s_390_, v_i_391_);
v___x_419_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_420_ = lean_uint8_dec_le(v___x_419_, v_c_399_);
if (v___x_420_ == 0)
{
goto v___jp_414_;
}
else
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_422_ = lean_uint8_dec_le(v_c_399_, v___x_421_);
if (v___x_422_ == 0)
{
goto v___jp_414_;
}
else
{
goto v___jp_392_;
}
}
v___jp_400_:
{
uint8_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_402_ = lean_uint8_dec_eq(v_c_399_, v___x_401_);
if (v___x_402_ == 0)
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__0, &l_Lean_isIdRestAscii___closed__0_once, _init_l_Lean_isIdRestAscii___closed__0);
v___x_404_ = lean_uint8_dec_eq(v_c_399_, v___x_403_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__1, &l_Lean_isIdRestAscii___closed__1_once, _init_l_Lean_isIdRestAscii___closed__1);
v___x_406_ = lean_uint8_dec_eq(v_c_399_, v___x_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_uint8_once(&l_Lean_isIdRestAscii___closed__2, &l_Lean_isIdRestAscii___closed__2_once, _init_l_Lean_isIdRestAscii___closed__2);
v___x_408_ = lean_uint8_dec_eq(v_c_399_, v___x_407_);
if (v___x_408_ == 0)
{
lean_dec(v_i_391_);
return v___x_408_;
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
}
v___jp_409_:
{
uint8_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0);
v___x_411_ = lean_uint8_dec_le(v___x_410_, v_c_399_);
if (v___x_411_ == 0)
{
goto v___jp_400_;
}
else
{
uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1);
v___x_413_ = lean_uint8_dec_le(v_c_399_, v___x_412_);
if (v___x_413_ == 0)
{
goto v___jp_400_;
}
else
{
goto v___jp_392_;
}
}
}
v___jp_414_:
{
uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_416_ = lean_uint8_dec_le(v___x_415_, v_c_399_);
if (v___x_416_ == 0)
{
goto v___jp_409_;
}
else
{
uint8_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_418_ = lean_uint8_dec_le(v_c_399_, v___x_417_);
if (v___x_418_ == 0)
{
goto v___jp_409_;
}
else
{
goto v___jp_392_;
}
}
}
}
v___jp_392_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_i_391_, v___x_393_);
lean_dec(v_i_391_);
v_i_391_ = v___x_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* v_s_423_, lean_object* v_i_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_423_, v_i_424_);
lean_dec_ref(v_s_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* v_s_427_){
_start:
{
lean_object* v___x_431_; uint8_t v_c_432_; uint8_t v___x_441_; uint8_t v___x_442_; 
v___x_431_ = lean_unsigned_to_nat(0u);
v_c_432_ = lean_string_get_byte_fast(v_s_427_, v___x_431_);
v___x_441_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_442_ = lean_uint8_dec_le(v___x_441_, v_c_432_);
if (v___x_442_ == 0)
{
goto v___jp_436_;
}
else
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_444_ = lean_uint8_dec_le(v_c_432_, v___x_443_);
if (v___x_444_ == 0)
{
goto v___jp_436_;
}
else
{
goto v___jp_428_;
}
}
v___jp_428_:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_427_, v___x_429_);
return v___x_430_;
}
v___jp_433_:
{
uint8_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_435_ = lean_uint8_dec_eq(v_c_432_, v___x_434_);
if (v___x_435_ == 0)
{
return v___x_435_;
}
else
{
goto v___jp_428_;
}
}
v___jp_436_:
{
uint8_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_438_ = lean_uint8_dec_le(v___x_437_, v_c_432_);
if (v___x_438_ == 0)
{
goto v___jp_433_;
}
else
{
uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_440_ = lean_uint8_dec_le(v_c_432_, v___x_439_);
if (v___x_440_ == 0)
{
goto v___jp_433_;
}
else
{
goto v___jp_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* v_s_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_445_);
lean_dec_ref(v_s_445_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* v_s_448_, lean_object* v_h_449_){
_start:
{
lean_object* v___x_453_; uint8_t v_c_454_; uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v_c_454_ = lean_string_get_byte_fast(v_s_448_, v___x_453_);
v___x_463_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_464_ = lean_uint8_dec_le(v___x_463_, v_c_454_);
if (v___x_464_ == 0)
{
goto v___jp_458_;
}
else
{
uint8_t v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_466_ = lean_uint8_dec_le(v_c_454_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_458_;
}
else
{
goto v___jp_450_;
}
}
v___jp_450_:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_448_, v___x_451_);
return v___x_452_;
}
v___jp_455_:
{
uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_457_ = lean_uint8_dec_eq(v_c_454_, v___x_456_);
if (v___x_457_ == 0)
{
return v___x_457_;
}
else
{
goto v___jp_450_;
}
}
v___jp_458_:
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_460_ = lean_uint8_dec_le(v___x_459_, v_c_454_);
if (v___x_460_ == 0)
{
goto v___jp_455_;
}
else
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_462_ = lean_uint8_dec_le(v_c_454_, v___x_461_);
if (v___x_462_ == 0)
{
goto v___jp_455_;
}
else
{
goto v___jp_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* v_s_467_, lean_object* v_h_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(v_s_467_, v_h_468_);
lean_dec_ref(v_s_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* v_s_472_){
_start:
{
uint32_t v___y_482_; uint32_t v___y_487_; uint8_t v___y_488_; lean_object* v___x_503_; uint8_t v_c_504_; uint8_t v___x_513_; uint8_t v___x_514_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v_c_504_ = lean_string_get_byte_fast(v_s_472_, v___x_503_);
v___x_513_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_514_ = lean_uint8_dec_le(v___x_513_, v_c_504_);
if (v___x_514_ == 0)
{
goto v___jp_508_;
}
else
{
uint8_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_516_ = lean_uint8_dec_le(v_c_504_, v___x_515_);
if (v___x_516_ == 0)
{
goto v___jp_508_;
}
else
{
goto v___jp_500_;
}
}
v___jp_473_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_string_utf8_byte_size(v_s_472_);
v___x_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_476_, 0, v_s_472_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_substring_drop(v___x_476_, v___x_477_);
v___x_479_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_480_ = lean_substring_all(v___x_478_, v___x_479_);
return v___x_480_;
}
v___jp_481_:
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 95;
v___x_484_ = lean_uint32_dec_eq(v___y_482_, v___x_483_);
if (v___x_484_ == 0)
{
uint8_t v___x_485_; 
v___x_485_ = l_Lean_isLetterLike(v___y_482_);
if (v___x_485_ == 0)
{
lean_dec_ref(v_s_472_);
return v___x_485_;
}
else
{
goto v___jp_473_;
}
}
else
{
goto v___jp_473_;
}
}
v___jp_486_:
{
if (v___y_488_ == 0)
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 97;
v___x_490_ = lean_uint32_dec_le(v___x_489_, v___y_487_);
if (v___x_490_ == 0)
{
v___y_482_ = v___y_487_;
goto v___jp_481_;
}
else
{
uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_491_ = 122;
v___x_492_ = lean_uint32_dec_le(v___y_487_, v___x_491_);
if (v___x_492_ == 0)
{
v___y_482_ = v___y_487_;
goto v___jp_481_;
}
else
{
goto v___jp_473_;
}
}
}
else
{
goto v___jp_473_;
}
}
v___jp_493_:
{
lean_object* v___x_494_; uint32_t v___x_495_; uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_string_utf8_get(v_s_472_, v___x_494_);
v___x_496_ = 65;
v___x_497_ = lean_uint32_dec_le(v___x_496_, v___x_495_);
if (v___x_497_ == 0)
{
v___y_487_ = v___x_495_;
v___y_488_ = v___x_497_;
goto v___jp_486_;
}
else
{
uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 90;
v___x_499_ = lean_uint32_dec_le(v___x_495_, v___x_498_);
v___y_487_ = v___x_495_;
v___y_488_ = v___x_499_;
goto v___jp_486_;
}
}
v___jp_500_:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_472_, v___x_501_);
if (v___x_502_ == 0)
{
goto v___jp_493_;
}
else
{
lean_dec_ref(v_s_472_);
return v___x_502_;
}
}
v___jp_505_:
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_507_ = lean_uint8_dec_eq(v_c_504_, v___x_506_);
if (v___x_507_ == 0)
{
goto v___jp_493_;
}
else
{
goto v___jp_500_;
}
}
v___jp_508_:
{
uint8_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_510_ = lean_uint8_dec_le(v___x_509_, v_c_504_);
if (v___x_510_ == 0)
{
goto v___jp_505_;
}
else
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_512_ = lean_uint8_dec_le(v_c_504_, v___x_511_);
if (v___x_512_ == 0)
{
goto v___jp_505_;
}
else
{
goto v___jp_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* v_s_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(v_s_517_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* v_s_520_, lean_object* v_h_521_){
_start:
{
uint32_t v___y_531_; uint32_t v___y_536_; uint8_t v___y_537_; lean_object* v___x_552_; uint8_t v_c_553_; uint8_t v___x_562_; uint8_t v___x_563_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v_c_553_ = lean_string_get_byte_fast(v_s_520_, v___x_552_);
v___x_562_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_563_ = lean_uint8_dec_le(v___x_562_, v_c_553_);
if (v___x_563_ == 0)
{
goto v___jp_557_;
}
else
{
uint8_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_565_ = lean_uint8_dec_le(v_c_553_, v___x_564_);
if (v___x_565_ == 0)
{
goto v___jp_557_;
}
else
{
goto v___jp_549_;
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_string_utf8_byte_size(v_s_520_);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v_s_520_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_substring_drop(v___x_525_, v___x_526_);
v___x_528_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_529_ = lean_substring_all(v___x_527_, v___x_528_);
return v___x_529_;
}
v___jp_530_:
{
uint32_t v___x_532_; uint8_t v___x_533_; 
v___x_532_ = 95;
v___x_533_ = lean_uint32_dec_eq(v___y_531_, v___x_532_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
v___x_534_ = l_Lean_isLetterLike(v___y_531_);
if (v___x_534_ == 0)
{
lean_dec_ref(v_s_520_);
return v___x_534_;
}
else
{
goto v___jp_522_;
}
}
else
{
goto v___jp_522_;
}
}
v___jp_535_:
{
if (v___y_537_ == 0)
{
uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 97;
v___x_539_ = lean_uint32_dec_le(v___x_538_, v___y_536_);
if (v___x_539_ == 0)
{
v___y_531_ = v___y_536_;
goto v___jp_530_;
}
else
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 122;
v___x_541_ = lean_uint32_dec_le(v___y_536_, v___x_540_);
if (v___x_541_ == 0)
{
v___y_531_ = v___y_536_;
goto v___jp_530_;
}
else
{
goto v___jp_522_;
}
}
}
else
{
goto v___jp_522_;
}
}
v___jp_542_:
{
lean_object* v___x_543_; uint32_t v___x_544_; uint32_t v___x_545_; uint8_t v___x_546_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_string_utf8_get(v_s_520_, v___x_543_);
v___x_545_ = 65;
v___x_546_ = lean_uint32_dec_le(v___x_545_, v___x_544_);
if (v___x_546_ == 0)
{
v___y_536_ = v___x_544_;
v___y_537_ = v___x_546_;
goto v___jp_535_;
}
else
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 90;
v___x_548_ = lean_uint32_dec_le(v___x_544_, v___x_547_);
v___y_536_ = v___x_544_;
v___y_537_ = v___x_548_;
goto v___jp_535_;
}
}
v___jp_549_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_520_, v___x_550_);
if (v___x_551_ == 0)
{
goto v___jp_542_;
}
else
{
lean_dec_ref(v_s_520_);
return v___x_551_;
}
}
v___jp_554_:
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_556_ = lean_uint8_dec_eq(v_c_553_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_542_;
}
else
{
goto v___jp_549_;
}
}
v___jp_557_:
{
uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_559_ = lean_uint8_dec_le(v___x_558_, v_c_553_);
if (v___x_559_ == 0)
{
goto v___jp_554_;
}
else
{
uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_561_ = lean_uint8_dec_le(v_c_553_, v___x_560_);
if (v___x_561_ == 0)
{
goto v___jp_554_;
}
else
{
goto v___jp_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* v_s_566_, lean_object* v_h_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(v_s_566_, v_h_567_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0(void){
_start:
{
uint32_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = 171;
v___x_571_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_572_ = lean_string_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1(void){
_start:
{
uint32_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = 187;
v___x_574_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_575_ = lean_string_push(v___x_574_, v___x_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* v_s_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_578_ = lean_string_append(v___x_577_, v_s_576_);
v___x_579_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* v_s_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Init_Meta_Defs_0__Lean_Name_escape(v_s_581_);
lean_dec_ref(v_s_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* v_s_584_, uint8_t v_force_585_){
_start:
{
uint8_t v___y_596_; uint32_t v___y_607_; uint32_t v___y_612_; uint8_t v___y_613_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_string_utf8_byte_size(v_s_584_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_632_ = lean_string_append(v___x_631_, v_s_584_);
lean_dec_ref(v_s_584_);
v___x_633_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
else
{
if (v_force_585_ == 0)
{
uint8_t v_c_636_; uint8_t v___x_645_; uint8_t v___x_646_; 
v_c_636_ = lean_string_get_byte_fast(v_s_584_, v___x_628_);
v___x_645_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_646_ = lean_uint8_dec_le(v___x_645_, v_c_636_);
if (v___x_646_ == 0)
{
goto v___jp_640_;
}
else
{
uint8_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_648_ = lean_uint8_dec_le(v_c_636_, v___x_647_);
if (v___x_648_ == 0)
{
goto v___jp_640_;
}
else
{
goto v___jp_625_;
}
}
v___jp_637_:
{
uint8_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_639_ = lean_uint8_dec_eq(v_c_636_, v___x_638_);
if (v___x_639_ == 0)
{
goto v___jp_618_;
}
else
{
goto v___jp_625_;
}
}
v___jp_640_:
{
uint8_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_642_ = lean_uint8_dec_le(v___x_641_, v_c_636_);
if (v___x_642_ == 0)
{
goto v___jp_637_;
}
else
{
uint8_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_644_ = lean_uint8_dec_le(v_c_636_, v___x_643_);
if (v___x_644_ == 0)
{
goto v___jp_637_;
}
else
{
goto v___jp_625_;
}
}
}
}
else
{
goto v___jp_586_;
}
}
v___jp_586_:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0));
lean_inc_ref(v_s_584_);
v___x_588_ = lean_string_any(v_s_584_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_589_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_590_ = lean_string_append(v___x_589_, v_s_584_);
lean_dec_ref(v_s_584_);
v___x_591_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; 
lean_dec_ref(v_s_584_);
v___x_594_ = lean_box(0);
return v___x_594_;
}
}
v___jp_595_:
{
if (v___y_596_ == 0)
{
goto v___jp_586_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_s_584_);
return v___x_597_;
}
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_string_utf8_byte_size(v_s_584_);
lean_inc_ref(v_s_584_);
v___x_601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_601_, 0, v_s_584_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_substring_drop(v___x_601_, v___x_602_);
v___x_604_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0));
v___x_605_ = lean_substring_all(v___x_603_, v___x_604_);
v___y_596_ = v___x_605_;
goto v___jp_595_;
}
v___jp_606_:
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 95;
v___x_609_ = lean_uint32_dec_eq(v___y_607_, v___x_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; 
v___x_610_ = l_Lean_isLetterLike(v___y_607_);
if (v___x_610_ == 0)
{
v___y_596_ = v___x_610_;
goto v___jp_595_;
}
else
{
goto v___jp_598_;
}
}
else
{
goto v___jp_598_;
}
}
v___jp_611_:
{
if (v___y_613_ == 0)
{
uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = 97;
v___x_615_ = lean_uint32_dec_le(v___x_614_, v___y_612_);
if (v___x_615_ == 0)
{
v___y_607_ = v___y_612_;
goto v___jp_606_;
}
else
{
uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 122;
v___x_617_ = lean_uint32_dec_le(v___y_612_, v___x_616_);
if (v___x_617_ == 0)
{
v___y_607_ = v___y_612_;
goto v___jp_606_;
}
else
{
goto v___jp_598_;
}
}
}
else
{
goto v___jp_598_;
}
}
v___jp_618_:
{
lean_object* v___x_619_; uint32_t v___x_620_; uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_string_utf8_get(v_s_584_, v___x_619_);
v___x_621_ = 65;
v___x_622_ = lean_uint32_dec_le(v___x_621_, v___x_620_);
if (v___x_622_ == 0)
{
v___y_612_ = v___x_620_;
v___y_613_ = v___x_622_;
goto v___jp_611_;
}
else
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 90;
v___x_624_ = lean_uint32_dec_le(v___x_620_, v___x_623_);
v___y_612_ = v___x_620_;
v___y_613_ = v___x_624_;
goto v___jp_611_;
}
}
v___jp_625_:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_584_, v___x_626_);
if (v___x_627_ == 0)
{
goto v___jp_618_;
}
else
{
v___y_596_ = v___x_627_;
goto v___jp_595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* v_s_649_, lean_object* v_force_650_){
_start:
{
uint8_t v_force_boxed_651_; lean_object* v_res_652_; 
v_force_boxed_651_ = lean_unbox(v_force_650_);
v_res_652_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(v_s_649_, v_force_boxed_651_);
return v_res_652_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t v___y_653_){
_start:
{
uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 187;
v___x_655_ = lean_uint32_dec_eq(v___y_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* v___y_656_){
_start:
{
uint32_t v___y_284__boxed_657_; uint8_t v_res_658_; lean_object* v_r_659_; 
v___y_284__boxed_657_ = lean_unbox_uint32(v___y_656_);
lean_dec(v___y_656_);
v_res_658_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(v___y_284__boxed_657_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t v___y_660_){
_start:
{
uint8_t v___y_678_; uint32_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 65;
v___x_684_ = lean_uint32_dec_le(v___x_683_, v___y_660_);
if (v___x_684_ == 0)
{
v___y_678_ = v___x_684_;
goto v___jp_677_;
}
else
{
uint32_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 90;
v___x_686_ = lean_uint32_dec_le(v___y_660_, v___x_685_);
v___y_678_ = v___x_686_;
goto v___jp_677_;
}
v___jp_661_:
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 95;
v___x_663_ = lean_uint32_dec_eq(v___y_660_, v___x_662_);
if (v___x_663_ == 0)
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 39;
v___x_665_ = lean_uint32_dec_eq(v___y_660_, v___x_664_);
if (v___x_665_ == 0)
{
uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 33;
v___x_667_ = lean_uint32_dec_eq(v___y_660_, v___x_666_);
if (v___x_667_ == 0)
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 63;
v___x_669_ = lean_uint32_dec_eq(v___y_660_, v___x_668_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = l_Lean_isLetterLike(v___y_660_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = l_Lean_isSubScriptAlnum(v___y_660_);
return v___x_671_;
}
else
{
return v___x_670_;
}
}
else
{
return v___x_669_;
}
}
else
{
return v___x_667_;
}
}
else
{
return v___x_665_;
}
}
else
{
return v___x_663_;
}
}
v___jp_672_:
{
uint32_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = 48;
v___x_674_ = lean_uint32_dec_le(v___x_673_, v___y_660_);
if (v___x_674_ == 0)
{
goto v___jp_661_;
}
else
{
uint32_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 57;
v___x_676_ = lean_uint32_dec_le(v___y_660_, v___x_675_);
if (v___x_676_ == 0)
{
goto v___jp_661_;
}
else
{
return v___x_676_;
}
}
}
v___jp_677_:
{
if (v___y_678_ == 0)
{
uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 97;
v___x_680_ = lean_uint32_dec_le(v___x_679_, v___y_660_);
if (v___x_680_ == 0)
{
goto v___jp_672_;
}
else
{
uint32_t v___x_681_; uint8_t v___x_682_; 
v___x_681_ = 122;
v___x_682_ = lean_uint32_dec_le(v___y_660_, v___x_681_);
if (v___x_682_ == 0)
{
goto v___jp_672_;
}
else
{
return v___x_682_;
}
}
}
else
{
return v___y_678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* v___y_687_){
_start:
{
uint32_t v___y_291__boxed_688_; uint8_t v_res_689_; lean_object* v_r_690_; 
v___y_291__boxed_688_ = lean_unbox_uint32(v___y_687_);
lean_dec(v___y_687_);
v_res_689_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(v___y_291__boxed_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t v_escape_693_, lean_object* v_s_694_, uint8_t v_force_695_){
_start:
{
if (v_escape_693_ == 0)
{
return v_s_694_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_string_utf8_byte_size(v_s_694_);
v___x_698_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_700_ = lean_string_append(v___x_699_, v_s_694_);
lean_dec_ref(v_s_694_);
v___x_701_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
return v___x_702_;
}
else
{
lean_object* v___f_703_; uint8_t v___y_711_; 
v___f_703_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
if (v_force_695_ == 0)
{
lean_object* v___f_712_; uint32_t v___y_719_; uint32_t v___y_724_; uint8_t v___y_725_; uint8_t v_c_739_; uint8_t v___x_748_; uint8_t v___x_749_; 
v___f_712_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_739_ = lean_string_get_byte_fast(v_s_694_, v___x_696_);
v___x_748_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_749_ = lean_uint8_dec_le(v___x_748_, v_c_739_);
if (v___x_749_ == 0)
{
goto v___jp_743_;
}
else
{
uint8_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_751_ = lean_uint8_dec_le(v_c_739_, v___x_750_);
if (v___x_751_ == 0)
{
goto v___jp_743_;
}
else
{
goto v___jp_736_;
}
}
v___jp_713_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
lean_inc_ref(v_s_694_);
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v_s_694_);
lean_ctor_set(v___x_714_, 1, v___x_696_);
lean_ctor_set(v___x_714_, 2, v___x_697_);
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_substring_drop(v___x_714_, v___x_715_);
v___x_717_ = lean_substring_all(v___x_716_, v___f_712_);
v___y_711_ = v___x_717_;
goto v___jp_710_;
}
v___jp_718_:
{
uint32_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 95;
v___x_721_ = lean_uint32_dec_eq(v___y_719_, v___x_720_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_isLetterLike(v___y_719_);
if (v___x_722_ == 0)
{
v___y_711_ = v___x_722_;
goto v___jp_710_;
}
else
{
goto v___jp_713_;
}
}
else
{
goto v___jp_713_;
}
}
v___jp_723_:
{
if (v___y_725_ == 0)
{
uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 97;
v___x_727_ = lean_uint32_dec_le(v___x_726_, v___y_724_);
if (v___x_727_ == 0)
{
v___y_719_ = v___y_724_;
goto v___jp_718_;
}
else
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 122;
v___x_729_ = lean_uint32_dec_le(v___y_724_, v___x_728_);
if (v___x_729_ == 0)
{
v___y_719_ = v___y_724_;
goto v___jp_718_;
}
else
{
goto v___jp_713_;
}
}
}
else
{
goto v___jp_713_;
}
}
v___jp_730_:
{
uint32_t v___x_731_; uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_string_utf8_get(v_s_694_, v___x_696_);
v___x_732_ = 65;
v___x_733_ = lean_uint32_dec_le(v___x_732_, v___x_731_);
if (v___x_733_ == 0)
{
v___y_724_ = v___x_731_;
v___y_725_ = v___x_733_;
goto v___jp_723_;
}
else
{
uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 90;
v___x_735_ = lean_uint32_dec_le(v___x_731_, v___x_734_);
v___y_724_ = v___x_731_;
v___y_725_ = v___x_735_;
goto v___jp_723_;
}
}
v___jp_736_:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_s_694_, v___x_737_);
if (v___x_738_ == 0)
{
goto v___jp_730_;
}
else
{
v___y_711_ = v___x_738_;
goto v___jp_710_;
}
}
v___jp_740_:
{
uint8_t v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_742_ = lean_uint8_dec_eq(v_c_739_, v___x_741_);
if (v___x_742_ == 0)
{
goto v___jp_730_;
}
else
{
goto v___jp_736_;
}
}
v___jp_743_:
{
uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_745_ = lean_uint8_dec_le(v___x_744_, v_c_739_);
if (v___x_745_ == 0)
{
goto v___jp_740_;
}
else
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_747_ = lean_uint8_dec_le(v_c_739_, v___x_746_);
if (v___x_747_ == 0)
{
goto v___jp_740_;
}
else
{
goto v___jp_736_;
}
}
}
}
else
{
goto v___jp_704_;
}
v___jp_704_:
{
uint8_t v___x_705_; 
lean_inc_ref(v_s_694_);
v___x_705_ = lean_string_any(v_s_694_, v___f_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_707_ = lean_string_append(v___x_706_, v_s_694_);
lean_dec_ref(v_s_694_);
v___x_708_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_709_ = lean_string_append(v___x_707_, v___x_708_);
return v___x_709_;
}
else
{
return v_s_694_;
}
}
v___jp_710_:
{
if (v___y_711_ == 0)
{
goto v___jp_704_;
}
else
{
return v_s_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* v_escape_752_, lean_object* v_s_753_, lean_object* v_force_754_){
_start:
{
uint8_t v_escape_boxed_755_; uint8_t v_force_boxed_756_; lean_object* v_res_757_; 
v_escape_boxed_755_ = lean_unbox(v_escape_752_);
v_force_boxed_756_ = lean_unbox(v_force_754_);
v_res_757_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_boxed_755_, v_s_753_, v_force_boxed_756_);
return v_res_757_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* v_x_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = 0;
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(v_x_760_);
lean_dec_ref(v_x_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* v_sep_765_, uint8_t v_escape_766_, lean_object* v_n_767_, lean_object* v_isToken_768_){
_start:
{
switch(lean_obj_tag(v_n_767_))
{
case 0:
{
lean_object* v___x_769_; 
lean_dec_ref(v_isToken_768_);
v___x_769_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_769_;
}
case 1:
{
lean_object* v_pre_770_; 
v_pre_770_ = lean_ctor_get(v_n_767_, 0);
if (lean_obj_tag(v_pre_770_) == 0)
{
lean_object* v_str_771_; lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; 
v_str_771_ = lean_ctor_get(v_n_767_, 1);
lean_inc_ref_n(v_str_771_, 2);
lean_dec_ref_known(v_n_767_, 2);
v___x_772_ = lean_apply_1(v_isToken_768_, v_str_771_);
v___x_773_ = lean_unbox(v___x_772_);
v___x_774_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_771_, v___x_773_);
return v___x_774_;
}
else
{
lean_object* v_str_775_; lean_object* v_r_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v_r_x27_780_; 
lean_inc(v_pre_770_);
v_str_775_ = lean_ctor_get(v_n_767_, 1);
lean_inc_ref_n(v_str_775_, 2);
lean_dec_ref_known(v_n_767_, 2);
lean_inc_ref(v_isToken_768_);
v_r_776_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_765_, v_escape_766_, v_pre_770_, v_isToken_768_);
v___x_777_ = lean_string_append(v_r_776_, v_sep_765_);
v___x_778_ = 0;
v___x_779_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_775_, v___x_778_);
lean_inc_ref(v___x_777_);
v_r_x27_780_ = lean_string_append(v___x_777_, v___x_779_);
lean_dec_ref(v___x_779_);
if (v_escape_766_ == 0)
{
lean_dec_ref(v___x_777_);
lean_dec_ref(v_str_775_);
lean_dec_ref(v_isToken_768_);
return v_r_x27_780_;
}
else
{
lean_object* v___x_781_; uint8_t v___x_782_; 
lean_inc_ref(v_r_x27_780_);
v___x_781_ = lean_apply_1(v_isToken_768_, v_r_x27_780_);
v___x_782_ = lean_unbox(v___x_781_);
if (v___x_782_ == 0)
{
lean_dec_ref(v___x_777_);
lean_dec_ref(v_str_775_);
return v_r_x27_780_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v_r_x27_780_);
v___x_783_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_766_, v_str_775_, v_escape_766_);
v___x_784_ = lean_string_append(v___x_777_, v___x_783_);
lean_dec_ref(v___x_783_);
return v___x_784_;
}
}
}
}
default: 
{
lean_object* v_pre_785_; 
lean_dec_ref(v_isToken_768_);
v_pre_785_ = lean_ctor_get(v_n_767_, 0);
if (lean_obj_tag(v_pre_785_) == 0)
{
lean_object* v_i_786_; lean_object* v___x_787_; 
v_i_786_ = lean_ctor_get(v_n_767_, 1);
lean_inc(v_i_786_);
lean_dec_ref_known(v_n_767_, 2);
v___x_787_ = l_Nat_reprFast(v_i_786_);
return v___x_787_;
}
else
{
lean_object* v_i_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_inc(v_pre_785_);
v_i_788_ = lean_ctor_get(v_n_767_, 1);
lean_inc(v_i_788_);
lean_dec_ref_known(v_n_767_, 2);
v___f_789_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1));
v___x_790_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_765_, v_escape_766_, v_pre_785_, v___f_789_);
v___x_791_ = lean_string_append(v___x_790_, v_sep_765_);
v___x_792_ = l_Nat_reprFast(v_i_788_);
v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
lean_dec_ref(v___x_792_);
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* v_sep_794_, lean_object* v_escape_795_, lean_object* v_n_796_, lean_object* v_isToken_797_){
_start:
{
uint8_t v_escape_boxed_798_; lean_object* v_res_799_; 
v_escape_boxed_798_ = lean_unbox(v_escape_795_);
v_res_799_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v_sep_794_, v_escape_boxed_798_, v_n_796_, v_isToken_797_);
lean_dec_ref(v_sep_794_);
return v_res_799_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* v_n_805_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; uint8_t v___x_808_; 
v___x_806_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1));
v___x_807_ = lean_name_eq(v_n_805_, v___x_806_);
v___x_808_ = 1;
if (v___x_807_ == 0)
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Name_getRoot(v_n_805_);
if (lean_obj_tag(v___x_809_) == 1)
{
lean_object* v_str_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_str_810_ = lean_ctor_get(v___x_809_, 1);
lean_inc_ref_n(v_str_810_, 2);
lean_dec_ref_known(v___x_809_, 2);
v___x_811_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2));
v___x_812_ = lean_string_isprefixof(v___x_811_, v_str_810_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3));
v___x_814_ = lean_string_isprefixof(v___x_813_, v_str_810_);
return v___x_814_;
}
else
{
lean_dec_ref(v_str_810_);
return v___x_808_;
}
}
else
{
lean_dec(v___x_809_);
return v___x_807_;
}
}
else
{
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* v_n_815_){
_start:
{
uint8_t v_res_816_; lean_object* v_r_817_; 
v_res_816_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_815_);
lean_dec(v_n_815_);
v_r_817_ = lean_box(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* v_n_818_, uint8_t v_escape_819_, lean_object* v_isToken_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_819_ == 0)
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v_escape_819_, v_n_818_, v_isToken_820_);
return v___x_822_;
}
else
{
uint8_t v___x_823_; 
lean_inc(v_n_818_);
v___x_823_ = l_Lean_Name_isInaccessibleUserName(v_n_818_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Name_hasMacroScopes(v_n_818_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; 
v___x_825_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_818_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v_escape_819_, v_n_818_, v_isToken_820_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_824_, v_n_818_, v_isToken_820_);
return v___x_827_;
}
}
else
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_823_, v_n_818_, v_isToken_820_);
return v___x_828_;
}
}
else
{
uint8_t v___x_829_; lean_object* v___x_830_; 
v___x_829_ = 0;
v___x_830_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(v___x_821_, v___x_829_, v_n_818_, v_isToken_820_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* v_n_831_, lean_object* v_escape_832_, lean_object* v_isToken_833_){
_start:
{
uint8_t v_escape_boxed_834_; lean_object* v_res_835_; 
v_escape_boxed_834_ = lean_unbox(v_escape_832_);
v_res_835_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(v_n_831_, v_escape_boxed_834_, v_isToken_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* v_sep_836_, uint8_t v_escape_837_, lean_object* v_n_838_){
_start:
{
switch(lean_obj_tag(v_n_838_))
{
case 0:
{
lean_object* v___x_839_; 
v___x_839_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0));
return v___x_839_;
}
case 1:
{
lean_object* v_pre_840_; 
v_pre_840_ = lean_ctor_get(v_n_838_, 0);
if (lean_obj_tag(v_pre_840_) == 0)
{
lean_object* v_str_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v_str_841_ = lean_ctor_get(v_n_838_, 1);
lean_inc_ref(v_str_841_);
lean_dec_ref_known(v_n_838_, 2);
v___x_842_ = 0;
v___x_843_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_837_, v_str_841_, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v_str_844_; lean_object* v_r_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v_r_x27_849_; 
lean_inc(v_pre_840_);
v_str_844_ = lean_ctor_get(v_n_838_, 1);
lean_inc_ref(v_str_844_);
lean_dec_ref_known(v_n_838_, 2);
v_r_845_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_836_, v_escape_837_, v_pre_840_);
v___x_846_ = lean_string_append(v_r_845_, v_sep_836_);
v___x_847_ = 0;
v___x_848_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(v_escape_837_, v_str_844_, v___x_847_);
v_r_x27_849_ = lean_string_append(v___x_846_, v___x_848_);
lean_dec_ref(v___x_848_);
return v_r_x27_849_;
}
}
default: 
{
lean_object* v_pre_850_; 
v_pre_850_ = lean_ctor_get(v_n_838_, 0);
if (lean_obj_tag(v_pre_850_) == 0)
{
lean_object* v_i_851_; lean_object* v___x_852_; 
v_i_851_ = lean_ctor_get(v_n_838_, 1);
lean_inc(v_i_851_);
lean_dec_ref_known(v_n_838_, 2);
v___x_852_ = l_Nat_reprFast(v_i_851_);
return v___x_852_;
}
else
{
lean_object* v_i_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc(v_pre_850_);
v_i_853_ = lean_ctor_get(v_n_838_, 1);
lean_inc(v_i_853_);
lean_dec_ref_known(v_n_838_, 2);
v___x_854_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_836_, v_escape_837_, v_pre_850_);
v___x_855_ = lean_string_append(v___x_854_, v_sep_836_);
v___x_856_ = l_Nat_reprFast(v_i_853_);
v___x_857_ = lean_string_append(v___x_855_, v___x_856_);
lean_dec_ref(v___x_856_);
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* v_sep_858_, lean_object* v_escape_859_, lean_object* v_n_860_){
_start:
{
uint8_t v_escape_boxed_861_; lean_object* v_res_862_; 
v_escape_boxed_861_ = lean_unbox(v_escape_859_);
v_res_862_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v_sep_858_, v_escape_boxed_861_, v_n_860_);
lean_dec_ref(v_sep_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* v_n_863_, uint8_t v_escape_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
if (v_escape_864_ == 0)
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v_escape_864_, v_n_863_);
return v___x_866_;
}
else
{
uint8_t v___x_867_; 
lean_inc(v_n_863_);
v___x_867_ = l_Lean_Name_isInaccessibleUserName(v_n_863_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; 
v___x_868_ = l_Lean_Name_hasMacroScopes(v_n_863_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(v_n_863_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v_escape_864_, v_n_863_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_868_, v_n_863_);
return v___x_871_;
}
}
else
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_867_, v_n_863_);
return v___x_872_;
}
}
else
{
uint8_t v___x_873_; lean_object* v___x_874_; 
v___x_873_ = 0;
v___x_874_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(v___x_865_, v___x_873_, v_n_863_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* v_n_875_, lean_object* v_escape_876_){
_start:
{
uint8_t v_escape_boxed_877_; lean_object* v_res_878_; 
v_escape_boxed_877_ = lean_unbox(v_escape_876_);
v_res_878_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_875_, v_escape_boxed_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* v_n_879_, uint8_t v_escape_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_879_, v_escape_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* v_n_882_, lean_object* v_escape_883_){
_start:
{
uint8_t v_escape_boxed_884_; lean_object* v_res_885_; 
v_escape_boxed_884_ = lean_unbox(v_escape_883_);
v_res_885_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(v_n_882_, v_escape_boxed_884_);
return v_res_885_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* v_x_886_){
_start:
{
switch(lean_obj_tag(v_x_886_))
{
case 0:
{
uint8_t v___x_887_; 
v___x_887_ = 0;
return v___x_887_;
}
case 1:
{
lean_object* v_pre_888_; 
v_pre_888_ = lean_ctor_get(v_x_886_, 0);
v_x_886_ = v_pre_888_;
goto _start;
}
default: 
{
uint8_t v___x_890_; 
v___x_890_ = 1;
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* v_x_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_x_891_);
lean_dec(v_x_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* v_n_909_, lean_object* v_prec_910_){
_start:
{
switch(lean_obj_tag(v_n_909_))
{
case 0:
{
lean_object* v___x_911_; 
v___x_911_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__1));
return v___x_911_;
}
case 1:
{
lean_object* v_pre_912_; lean_object* v_str_913_; uint8_t v___x_914_; 
v_pre_912_ = lean_ctor_get(v_n_909_, 0);
v_str_913_ = lean_ctor_get(v_n_909_, 1);
v___x_914_ = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(v_pre_912_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = 1;
v___x_916_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__3));
v___x_917_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_n_909_, v___x_915_);
v___x_918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_inc_ref(v_str_913_);
lean_inc(v_pre_912_);
lean_dec_ref_known(v_n_909_, 2);
v___x_920_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__5));
v___x_921_ = lean_unsigned_to_nat(1024u);
v___x_922_ = l_Lean_Name_reprPrec(v_pre_912_, v___x_921_);
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_920_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l_String_quote(v_str_913_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_925_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Repr_addAppParen(v___x_928_, v_prec_910_);
return v___x_929_;
}
}
default: 
{
lean_object* v_pre_930_; lean_object* v_i_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_pre_930_ = lean_ctor_get(v_n_909_, 0);
lean_inc(v_pre_930_);
v_i_931_ = lean_ctor_get(v_n_909_, 1);
lean_inc(v_i_931_);
lean_dec_ref_known(v_n_909_, 2);
v___x_932_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__9));
v___x_933_ = lean_unsigned_to_nat(1024u);
v___x_934_ = l_Lean_Name_reprPrec(v_pre_930_, v___x_933_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__7));
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Nat_reprFast(v_i_931_);
v___x_939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_937_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Repr_addAppParen(v___x_940_, v_prec_910_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* v_n_942_, lean_object* v_prec_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Name_reprPrec(v_n_942_, v_prec_943_);
lean_dec(v_prec_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_947_) == 1)
{
lean_object* v_pre_948_; lean_object* v_str_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_pre_948_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_pre_948_);
v_str_949_ = lean_ctor_get(v_x_947_, 1);
lean_inc_ref(v_str_949_);
lean_dec_ref_known(v_x_947_, 2);
v___x_950_ = lean_string_capitalize(v_str_949_);
v___x_951_ = l_Lean_Name_str___override(v_pre_948_, v___x_950_);
return v___x_951_;
}
else
{
return v_x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
switch(lean_obj_tag(v_x_952_))
{
case 0:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_inc(v_x_954_);
return v_x_954_;
}
else
{
return v_x_952_;
}
}
case 1:
{
lean_object* v_pre_955_; lean_object* v_str_956_; uint8_t v___x_957_; 
v_pre_955_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_pre_955_);
v_str_956_ = lean_ctor_get(v_x_952_, 1);
lean_inc_ref(v_str_956_);
v___x_957_ = lean_name_eq(v_x_952_, v_x_953_);
lean_dec_ref_known(v_x_952_, 2);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = l_Lean_Name_replacePrefix(v_pre_955_, v_x_953_, v_x_954_);
v___x_959_ = l_Lean_Name_str___override(v___x_958_, v_str_956_);
return v___x_959_;
}
else
{
lean_dec_ref(v_str_956_);
lean_dec(v_pre_955_);
lean_inc(v_x_954_);
return v_x_954_;
}
}
default: 
{
lean_object* v_pre_960_; lean_object* v_i_961_; uint8_t v___x_962_; 
v_pre_960_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_pre_960_);
v_i_961_ = lean_ctor_get(v_x_952_, 1);
lean_inc(v_i_961_);
v___x_962_ = lean_name_eq(v_x_952_, v_x_953_);
lean_dec_ref_known(v_x_952_, 2);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = l_Lean_Name_replacePrefix(v_pre_960_, v_x_953_, v_x_954_);
v___x_964_ = l_Lean_Name_num___override(v___x_963_, v_i_961_);
return v___x_964_;
}
else
{
lean_dec(v_i_961_);
lean_dec(v_pre_960_);
lean_inc(v_x_954_);
return v_x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Name_replacePrefix(v_x_965_, v_x_966_, v_x_967_);
lean_dec(v_x_967_);
lean_dec(v_x_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
switch(lean_obj_tag(v_x_970_))
{
case 0:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v_x_969_);
return v___x_971_;
}
case 1:
{
if (lean_obj_tag(v_x_969_) == 1)
{
lean_object* v_pre_972_; lean_object* v_str_973_; lean_object* v_pre_974_; lean_object* v_str_975_; uint8_t v___x_976_; 
v_pre_972_ = lean_ctor_get(v_x_970_, 0);
v_str_973_ = lean_ctor_get(v_x_970_, 1);
v_pre_974_ = lean_ctor_get(v_x_969_, 0);
lean_inc(v_pre_974_);
v_str_975_ = lean_ctor_get(v_x_969_, 1);
lean_inc_ref(v_str_975_);
lean_dec_ref_known(v_x_969_, 2);
v___x_976_ = lean_string_dec_eq(v_str_975_, v_str_973_);
lean_dec_ref(v_str_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec(v_pre_974_);
v___x_977_ = lean_box(0);
return v___x_977_;
}
else
{
v_x_969_ = v_pre_974_;
v_x_970_ = v_pre_972_;
goto _start;
}
}
else
{
lean_object* v___x_979_; 
lean_dec(v_x_969_);
v___x_979_ = lean_box(0);
return v___x_979_;
}
}
default: 
{
if (lean_obj_tag(v_x_969_) == 2)
{
lean_object* v_pre_980_; lean_object* v_i_981_; lean_object* v_pre_982_; lean_object* v_i_983_; uint8_t v___x_984_; 
v_pre_980_ = lean_ctor_get(v_x_970_, 0);
v_i_981_ = lean_ctor_get(v_x_970_, 1);
v_pre_982_ = lean_ctor_get(v_x_969_, 0);
lean_inc(v_pre_982_);
v_i_983_ = lean_ctor_get(v_x_969_, 1);
lean_inc(v_i_983_);
lean_dec_ref_known(v_x_969_, 2);
v___x_984_ = lean_nat_dec_eq(v_i_983_, v_i_981_);
lean_dec(v_i_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec(v_pre_982_);
v___x_985_ = lean_box(0);
return v___x_985_;
}
else
{
v_x_969_ = v_pre_982_;
v_x_970_ = v_pre_980_;
goto _start;
}
}
else
{
lean_object* v___x_987_; 
lean_dec(v_x_969_);
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Name_eraseSuffix_x3f(v_x_988_, v_x_989_);
lean_dec(v_x_989_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* v_n_991_, lean_object* v_f_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = l_Lean_Name_hasMacroScopes(v_n_991_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_apply_1(v_f_992_, v_n_991_);
return v___x_994_;
}
else
{
lean_object* v_view_995_; lean_object* v_name_996_; lean_object* v_imported_997_; lean_object* v_ctx_998_; lean_object* v_scopes_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1008_; 
v_view_995_ = l_Lean_extractMacroScopes(v_n_991_);
v_name_996_ = lean_ctor_get(v_view_995_, 0);
v_imported_997_ = lean_ctor_get(v_view_995_, 1);
v_ctx_998_ = lean_ctor_get(v_view_995_, 2);
v_scopes_999_ = lean_ctor_get(v_view_995_, 3);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_view_995_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1001_ = v_view_995_;
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_scopes_999_);
lean_inc(v_ctx_998_);
lean_inc(v_imported_997_);
lean_inc(v_name_996_);
lean_dec(v_view_995_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_apply_1(v_f_992_, v_name_996_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_imported_997_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_ctx_998_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_scopes_999_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_MacroScopesView_review(v___x_1005_);
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* v_suffix_1009_, lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 1)
{
lean_object* v_pre_1011_; lean_object* v_str_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_pre_1011_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_pre_1011_);
v_str_1012_ = lean_ctor_get(v_x_1010_, 1);
lean_inc_ref(v_str_1012_);
lean_dec_ref_known(v_x_1010_, 2);
v___x_1013_ = lean_string_append(v_str_1012_, v_suffix_1009_);
lean_dec_ref(v_suffix_1009_);
v___x_1014_ = l_Lean_Name_str___override(v_pre_1011_, v___x_1013_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Name_str___override(v_x_1010_, v_suffix_1009_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* v_n_1016_, lean_object* v_suffix_1017_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = l_Lean_Name_hasMacroScopes(v_n_1016_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1017_, v_n_1016_);
return v___x_1019_;
}
else
{
lean_object* v_view_1020_; lean_object* v_name_1021_; lean_object* v_imported_1022_; lean_object* v_ctx_1023_; lean_object* v_scopes_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1033_; 
v_view_1020_ = l_Lean_extractMacroScopes(v_n_1016_);
v_name_1021_ = lean_ctor_get(v_view_1020_, 0);
v_imported_1022_ = lean_ctor_get(v_view_1020_, 1);
v_ctx_1023_ = lean_ctor_get(v_view_1020_, 2);
v_scopes_1024_ = lean_ctor_get(v_view_1020_, 3);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_view_1020_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1026_ = v_view_1020_;
v_isShared_1027_ = v_isSharedCheck_1033_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_scopes_1024_);
lean_inc(v_ctx_1023_);
lean_inc(v_imported_1022_);
lean_inc(v_name_1021_);
lean_dec(v_view_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1033_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = l_Lean_Name_appendAfter___lam__0(v_suffix_1017_, v_name_1021_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_imported_1022_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_ctx_1023_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_scopes_1024_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_MacroScopesView_review(v___x_1030_);
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* v_idx_1034_, lean_object* v_x_1035_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 1)
{
lean_object* v_pre_1036_; lean_object* v_str_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_pre_1036_ = lean_ctor_get(v_x_1035_, 0);
lean_inc(v_pre_1036_);
v_str_1037_ = lean_ctor_get(v_x_1035_, 1);
lean_inc_ref(v_str_1037_);
lean_dec_ref_known(v_x_1035_, 2);
v___x_1038_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1039_ = lean_string_append(v_str_1037_, v___x_1038_);
v___x_1040_ = l_Nat_reprFast(v_idx_1034_);
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
lean_dec_ref(v___x_1040_);
v___x_1042_ = l_Lean_Name_str___override(v_pre_1036_, v___x_1041_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1043_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_1044_ = l_Nat_reprFast(v_idx_1034_);
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = l_Lean_Name_str___override(v_x_1035_, v___x_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* v_n_1047_, lean_object* v_idx_1048_){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = l_Lean_Name_hasMacroScopes(v_n_1047_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1048_, v_n_1047_);
return v___x_1050_;
}
else
{
lean_object* v_view_1051_; lean_object* v_name_1052_; lean_object* v_imported_1053_; lean_object* v_ctx_1054_; lean_object* v_scopes_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
v_view_1051_ = l_Lean_extractMacroScopes(v_n_1047_);
v_name_1052_ = lean_ctor_get(v_view_1051_, 0);
v_imported_1053_ = lean_ctor_get(v_view_1051_, 1);
v_ctx_1054_ = lean_ctor_get(v_view_1051_, 2);
v_scopes_1055_ = lean_ctor_get(v_view_1051_, 3);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_view_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1057_ = v_view_1051_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_scopes_1055_);
lean_inc(v_ctx_1054_);
lean_inc(v_imported_1053_);
lean_inc(v_name_1052_);
lean_dec(v_view_1051_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = l_Lean_Name_appendIndexAfter___lam__0(v_idx_1048_, v_name_1052_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_imported_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_ctx_1054_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_scopes_1055_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_MacroScopesView_review(v___x_1061_);
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* v_pre_1065_, lean_object* v_x_1066_){
_start:
{
switch(lean_obj_tag(v_x_1066_))
{
case 0:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Name_str___override(v_x_1066_, v_pre_1065_);
return v___x_1067_;
}
case 1:
{
lean_object* v_pre_1068_; lean_object* v_str_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_pre_1068_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_pre_1068_);
v_str_1069_ = lean_ctor_get(v_x_1066_, 1);
lean_inc_ref(v_str_1069_);
lean_dec_ref_known(v_x_1066_, 2);
v___x_1070_ = lean_string_append(v_pre_1065_, v_str_1069_);
lean_dec_ref(v_str_1069_);
v___x_1071_ = l_Lean_Name_str___override(v_pre_1068_, v___x_1070_);
return v___x_1071_;
}
default: 
{
lean_object* v_pre_1072_; lean_object* v_i_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_pre_1072_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_pre_1072_);
v_i_1073_ = lean_ctor_get(v_x_1066_, 1);
lean_inc(v_i_1073_);
lean_dec_ref_known(v_x_1066_, 2);
v___x_1074_ = l_Lean_Name_str___override(v_pre_1072_, v_pre_1065_);
v___x_1075_ = l_Lean_Name_num___override(v___x_1074_, v_i_1073_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_append_before(lean_object* v_n_1076_, lean_object* v_pre_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = l_Lean_Name_hasMacroScopes(v_n_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Name_appendBefore___lam__0(v_pre_1077_, v_n_1076_);
return v___x_1079_;
}
else
{
lean_object* v_view_1080_; lean_object* v_name_1081_; lean_object* v_imported_1082_; lean_object* v_ctx_1083_; lean_object* v_scopes_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
v_view_1080_ = l_Lean_extractMacroScopes(v_n_1076_);
v_name_1081_ = lean_ctor_get(v_view_1080_, 0);
v_imported_1082_ = lean_ctor_get(v_view_1080_, 1);
v_ctx_1083_ = lean_ctor_get(v_view_1080_, 2);
v_scopes_1084_ = lean_ctor_get(v_view_1080_, 3);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_view_1080_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1086_ = v_view_1080_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_scopes_1084_);
lean_inc(v_ctx_1083_);
lean_inc(v_imported_1082_);
lean_inc(v_name_1081_);
lean_dec(v_view_1080_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = l_Lean_Name_appendBefore___lam__0(v_pre_1077_, v_name_1081_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_imported_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_ctx_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_scopes_1084_);
v___x_1090_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_MacroScopesView_review(v___x_1090_);
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_h__1_1096_, lean_object* v_h__2_1097_, lean_object* v_h__3_1098_, lean_object* v_h__4_1099_){
_start:
{
switch(lean_obj_tag(v_x_1094_))
{
case 0:
{
lean_dec(v_h__3_1098_);
lean_dec(v_h__2_1097_);
if (lean_obj_tag(v_x_1095_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__4_1099_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_apply_1(v_h__1_1096_, v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
lean_dec(v_h__1_1096_);
v___x_1102_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1102_;
}
}
case 1:
{
lean_dec(v_h__3_1098_);
lean_dec(v_h__1_1096_);
if (lean_obj_tag(v_x_1095_) == 1)
{
lean_object* v_pre_1103_; lean_object* v_str_1104_; lean_object* v_pre_1105_; lean_object* v_str_1106_; lean_object* v___x_1107_; 
lean_dec(v_h__4_1099_);
v_pre_1103_ = lean_ctor_get(v_x_1094_, 0);
lean_inc(v_pre_1103_);
v_str_1104_ = lean_ctor_get(v_x_1094_, 1);
lean_inc_ref(v_str_1104_);
lean_dec_ref_known(v_x_1094_, 2);
v_pre_1105_ = lean_ctor_get(v_x_1095_, 0);
lean_inc(v_pre_1105_);
v_str_1106_ = lean_ctor_get(v_x_1095_, 1);
lean_inc_ref(v_str_1106_);
lean_dec_ref_known(v_x_1095_, 2);
v___x_1107_ = lean_apply_4(v_h__2_1097_, v_pre_1103_, v_str_1104_, v_pre_1105_, v_str_1106_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_h__2_1097_);
v___x_1108_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1108_;
}
}
default: 
{
lean_dec(v_h__2_1097_);
lean_dec(v_h__1_1096_);
if (lean_obj_tag(v_x_1095_) == 2)
{
lean_object* v_pre_1109_; lean_object* v_i_1110_; lean_object* v_pre_1111_; lean_object* v_i_1112_; lean_object* v___x_1113_; 
lean_dec(v_h__4_1099_);
v_pre_1109_ = lean_ctor_get(v_x_1094_, 0);
lean_inc(v_pre_1109_);
v_i_1110_ = lean_ctor_get(v_x_1094_, 1);
lean_inc(v_i_1110_);
lean_dec_ref_known(v_x_1094_, 2);
v_pre_1111_ = lean_ctor_get(v_x_1095_, 0);
lean_inc(v_pre_1111_);
v_i_1112_ = lean_ctor_get(v_x_1095_, 1);
lean_inc(v_i_1112_);
lean_dec_ref_known(v_x_1095_, 2);
v___x_1113_ = lean_apply_4(v_h__3_1098_, v_pre_1109_, v_i_1110_, v_pre_1111_, v_i_1112_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; 
lean_dec(v_h__3_1098_);
v___x_1114_ = lean_apply_5(v_h__4_1099_, v_x_1094_, v_x_1095_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* v_motive_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_h__1_1118_, lean_object* v_h__2_1119_, lean_object* v_h__3_1120_, lean_object* v_h__4_1121_){
_start:
{
switch(lean_obj_tag(v_x_1116_))
{
case 0:
{
lean_dec(v_h__3_1120_);
lean_dec(v_h__2_1119_);
if (lean_obj_tag(v_x_1117_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_h__4_1121_);
v___x_1122_ = lean_box(0);
v___x_1123_ = lean_apply_1(v_h__1_1118_, v___x_1122_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_h__1_1118_);
v___x_1124_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1124_;
}
}
case 1:
{
lean_dec(v_h__3_1120_);
lean_dec(v_h__1_1118_);
if (lean_obj_tag(v_x_1117_) == 1)
{
lean_object* v_pre_1125_; lean_object* v_str_1126_; lean_object* v_pre_1127_; lean_object* v_str_1128_; lean_object* v___x_1129_; 
lean_dec(v_h__4_1121_);
v_pre_1125_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_pre_1125_);
v_str_1126_ = lean_ctor_get(v_x_1116_, 1);
lean_inc_ref(v_str_1126_);
lean_dec_ref_known(v_x_1116_, 2);
v_pre_1127_ = lean_ctor_get(v_x_1117_, 0);
lean_inc(v_pre_1127_);
v_str_1128_ = lean_ctor_get(v_x_1117_, 1);
lean_inc_ref(v_str_1128_);
lean_dec_ref_known(v_x_1117_, 2);
v___x_1129_ = lean_apply_4(v_h__2_1119_, v_pre_1125_, v_str_1126_, v_pre_1127_, v_str_1128_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; 
lean_dec(v_h__2_1119_);
v___x_1130_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1130_;
}
}
default: 
{
lean_dec(v_h__2_1119_);
lean_dec(v_h__1_1118_);
if (lean_obj_tag(v_x_1117_) == 2)
{
lean_object* v_pre_1131_; lean_object* v_i_1132_; lean_object* v_pre_1133_; lean_object* v_i_1134_; lean_object* v___x_1135_; 
lean_dec(v_h__4_1121_);
v_pre_1131_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_pre_1131_);
v_i_1132_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_i_1132_);
lean_dec_ref_known(v_x_1116_, 2);
v_pre_1133_ = lean_ctor_get(v_x_1117_, 0);
lean_inc(v_pre_1133_);
v_i_1134_ = lean_ctor_get(v_x_1117_, 1);
lean_inc(v_i_1134_);
lean_dec_ref_known(v_x_1117_, 2);
v___x_1135_ = lean_apply_4(v_h__3_1120_, v_pre_1131_, v_i_1132_, v_pre_1133_, v_i_1134_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; 
lean_dec(v_h__3_1120_);
v___x_1136_ = lean_apply_5(v_h__4_1121_, v_x_1116_, v_x_1117_, lean_box(0), lean_box(0), lean_box(0));
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* v_a_1137_, lean_object* v_b_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_name_eq(v_a_1137_, v_b_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* v_a_1140_, lean_object* v_b_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Lean_Name_instDecidableEq(v_a_1140_, v_b_1141_);
lean_dec(v_b_1141_);
lean_dec(v_a_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* v_g_1144_){
_start:
{
lean_object* v_namePrefix_1145_; lean_object* v_idx_1146_; lean_object* v___x_1147_; 
v_namePrefix_1145_ = lean_ctor_get(v_g_1144_, 0);
lean_inc(v_namePrefix_1145_);
v_idx_1146_ = lean_ctor_get(v_g_1144_, 1);
lean_inc(v_idx_1146_);
lean_dec_ref(v_g_1144_);
v___x_1147_ = l_Lean_Name_num___override(v_namePrefix_1145_, v_idx_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* v_g_1148_){
_start:
{
lean_object* v_namePrefix_1149_; lean_object* v_idx_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1159_; 
v_namePrefix_1149_ = lean_ctor_get(v_g_1148_, 0);
v_idx_1150_ = lean_ctor_get(v_g_1148_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_g_1148_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1152_ = v_g_1148_;
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_idx_1150_);
lean_inc(v_namePrefix_1149_);
lean_dec(v_g_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_nat_add(v_idx_1150_, v___x_1154_);
lean_dec(v_idx_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_namePrefix_1149_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* v_g_1160_){
_start:
{
lean_object* v_namePrefix_1161_; lean_object* v_idx_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1174_; 
v_namePrefix_1161_ = lean_ctor_get(v_g_1160_, 0);
v_idx_1162_ = lean_ctor_get(v_g_1160_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_g_1160_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1164_ = v_g_1160_;
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_idx_1162_);
lean_inc(v_namePrefix_1161_);
lean_dec(v_g_1160_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1174_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_inc(v_idx_1162_);
lean_inc(v_namePrefix_1161_);
v___x_1166_ = l_Lean_Name_num___override(v_namePrefix_1161_, v_idx_1162_);
v___x_1167_ = lean_unsigned_to_nat(1u);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1167_);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_nat_add(v_idx_1162_, v___x_1167_);
lean_dec(v_idx_1162_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_namePrefix_1161_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* v_toPure_1175_, lean_object* v_r_1176_, lean_object* v_____r_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_apply_2(v_toPure_1175_, lean_box(0), v_r_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* v_toPure_1179_, lean_object* v_setNGen_1180_, lean_object* v_toBind_1181_, lean_object* v_ngen_1182_){
_start:
{
lean_object* v_namePrefix_1183_; lean_object* v_idx_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1197_; 
v_namePrefix_1183_ = lean_ctor_get(v_ngen_1182_, 0);
v_idx_1184_ = lean_ctor_get(v_ngen_1182_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_ngen_1182_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1186_ = v_ngen_1182_;
v_isShared_1187_ = v_isSharedCheck_1197_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_idx_1184_);
lean_inc(v_namePrefix_1183_);
lean_dec(v_ngen_1182_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1197_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_r_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_inc(v_idx_1184_);
lean_inc(v_namePrefix_1183_);
v_r_1188_ = l_Lean_Name_num___override(v_namePrefix_1183_, v_idx_1184_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1189_, 0, v_toPure_1179_);
lean_closure_set(v___f_1189_, 1, v_r_1188_);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_idx_1184_, v___x_1190_);
lean_dec(v_idx_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1191_);
v___x_1193_ = v___x_1186_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_namePrefix_1183_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_apply_1(v_setNGen_1180_, v___x_1193_);
v___x_1195_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1194_, v___f_1189_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* v_inst_1198_, lean_object* v_inst_1199_){
_start:
{
lean_object* v_toApplicative_1200_; lean_object* v_toBind_1201_; lean_object* v_getNGen_1202_; lean_object* v_setNGen_1203_; lean_object* v_toPure_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; 
v_toApplicative_1200_ = lean_ctor_get(v_inst_1198_, 0);
lean_inc_ref(v_toApplicative_1200_);
v_toBind_1201_ = lean_ctor_get(v_inst_1198_, 1);
lean_inc_n(v_toBind_1201_, 2);
lean_dec_ref(v_inst_1198_);
v_getNGen_1202_ = lean_ctor_get(v_inst_1199_, 0);
lean_inc(v_getNGen_1202_);
v_setNGen_1203_ = lean_ctor_get(v_inst_1199_, 1);
lean_inc(v_setNGen_1203_);
lean_dec_ref(v_inst_1199_);
v_toPure_1204_ = lean_ctor_get(v_toApplicative_1200_, 1);
lean_inc(v_toPure_1204_);
lean_dec_ref(v_toApplicative_1200_);
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1205_, 0, v_toPure_1204_);
lean_closure_set(v___f_1205_, 1, v_setNGen_1203_);
lean_closure_set(v___f_1205_, 2, v_toBind_1201_);
v___x_1206_ = lean_apply_4(v_toBind_1201_, lean_box(0), lean_box(0), v_getNGen_1202_, v___f_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_mkFreshId___redArg(v_inst_1208_, v_inst_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* v_setNGen_1211_, lean_object* v_inst_1212_, lean_object* v_ngen_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_apply_1(v_setNGen_1211_, v_ngen_1213_);
v___x_1215_ = lean_apply_2(v_inst_1212_, lean_box(0), v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_){
_start:
{
lean_object* v_getNGen_1218_; lean_object* v_setNGen_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1228_; 
v_getNGen_1218_ = lean_ctor_get(v_inst_1217_, 0);
v_setNGen_1219_ = lean_ctor_get(v_inst_1217_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_inst_1217_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1221_ = v_inst_1217_;
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_setNGen_1219_);
lean_inc(v_getNGen_1218_);
lean_dec(v_inst_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
lean_inc(v_inst_1216_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1223_, 0, v_setNGen_1219_);
lean_closure_set(v___f_1223_, 1, v_inst_1216_);
v___x_1224_ = lean_apply_2(v_inst_1216_, lean_box(0), v_getNGen_1218_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___f_1223_);
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v___f_1223_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* v_m_1229_, lean_object* v_n_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_monadNameGeneratorLift___redArg(v_inst_1231_, v_inst_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1236_) == 0)
{
lean_dec(v_x_1234_);
return v_x_1235_;
}
else
{
lean_object* v_head_1237_; lean_object* v_tail_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1249_; 
v_head_1237_ = lean_ctor_get(v_x_1236_, 0);
v_tail_1238_ = lean_ctor_get(v_x_1236_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1236_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1240_ = v_x_1236_;
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_tail_1238_);
lean_inc(v_head_1237_);
lean_dec(v_x_1236_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
lean_inc(v_x_1234_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 5);
lean_ctor_set(v___x_1240_, 1, v_x_1234_);
lean_ctor_set(v___x_1240_, 0, v_x_1235_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_x_1235_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_x_1234_);
v___x_1243_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = l_String_quote(v_head_1237_);
v___x_1245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1243_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v_x_1235_ = v___x_1246_;
v_x_1236_ = v_tail_1238_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_dec(v_x_1250_);
return v_x_1251_;
}
else
{
lean_object* v_head_1253_; lean_object* v_tail_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1265_; 
v_head_1253_ = lean_ctor_get(v_x_1252_, 0);
v_tail_1254_ = lean_ctor_get(v_x_1252_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1256_ = v_x_1252_;
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_tail_1254_);
lean_inc(v_head_1253_);
lean_dec(v_x_1252_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
lean_inc(v_x_1250_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 5);
lean_ctor_set(v___x_1256_, 1, v_x_1250_);
lean_ctor_set(v___x_1256_, 0, v_x_1251_);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_x_1251_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_x_1250_);
v___x_1259_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = l_String_quote(v_head_1253_);
v___x_1261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(v_x_1250_, v___x_1262_, v_tail_1254_);
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = l_String_quote(v___y_1266_);
v___x_1268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
lean_object* v___x_1271_; 
lean_dec(v_x_1270_);
v___x_1271_ = lean_box(0);
return v___x_1271_;
}
else
{
lean_object* v_tail_1272_; 
v_tail_1272_ = lean_ctor_get(v_x_1269_, 1);
if (lean_obj_tag(v_tail_1272_) == 0)
{
lean_object* v_head_1273_; lean_object* v___x_1274_; 
lean_dec(v_x_1270_);
v_head_1273_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_head_1273_);
lean_dec_ref_known(v_x_1269_, 2);
v___x_1274_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1273_);
return v___x_1274_;
}
else
{
lean_object* v_head_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_inc(v_tail_1272_);
v_head_1275_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_head_1275_);
lean_dec_ref_known(v_x_1269_, 2);
v___x_1276_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(v_head_1275_);
v___x_1277_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(v_x_1270_, v___x_1276_, v_tail_1272_);
return v___x_1277_;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2));
v___x_1290_ = lean_string_length(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
v___x_1292_ = lean_nat_to_int(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* v_a_1297_){
_start:
{
if (lean_obj_tag(v_a_1297_) == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1299_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1300_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(v_a_1297_, v___x_1299_);
v___x_1301_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1302_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1300_);
v___x_1304_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1301_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Std_Format_fill(v___x_1306_);
return v___x_1307_;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_unsigned_to_nat(2u);
v___x_1315_ = lean_nat_to_int(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_to_int(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* v_x_1324_, lean_object* v_prec_1325_){
_start:
{
if (lean_obj_tag(v_x_1324_) == 0)
{
lean_object* v_ns_1326_; lean_object* v___y_1328_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_ns_1326_ = lean_ctor_get(v_x_1324_, 0);
lean_inc(v_ns_1326_);
lean_dec_ref_known(v_x_1324_, 1);
v___x_1337_ = lean_unsigned_to_nat(1024u);
v___x_1338_ = lean_nat_dec_le(v___x_1337_, v_prec_1325_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1328_ = v___x_1339_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1328_ = v___x_1340_;
goto v___jp_1327_;
}
v___jp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1329_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__2));
v___x_1330_ = lean_unsigned_to_nat(1024u);
v___x_1331_ = l_Lean_Name_reprPrec(v_ns_1326_, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1329_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
lean_inc(v___y_1328_);
v___x_1333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___y_1328_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = 0;
v___x_1335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*1, v___x_1334_);
v___x_1336_ = l_Repr_addAppParen(v___x_1335_, v_prec_1325_);
return v___x_1336_;
}
}
else
{
lean_object* v_n_1341_; lean_object* v_fields_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1366_; 
v_n_1341_ = lean_ctor_get(v_x_1324_, 0);
v_fields_1342_ = lean_ctor_get(v_x_1324_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_x_1324_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1344_ = v_x_1324_;
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_fields_1342_);
lean_inc(v_n_1341_);
lean_dec(v_x_1324_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1366_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___y_1347_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_unsigned_to_nat(1024u);
v___x_1363_ = lean_nat_dec_le(v___x_1362_, v_prec_1325_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1347_ = v___x_1364_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1347_ = v___x_1365_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1348_ = lean_box(1);
v___x_1349_ = ((lean_object*)(l_Lean_Syntax_instReprPreresolved_repr___closed__7));
v___x_1350_ = lean_unsigned_to_nat(1024u);
v___x_1351_ = l_Lean_Name_reprPrec(v_n_1341_, v___x_1350_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 5);
lean_ctor_set(v___x_1344_, 1, v___x_1351_);
lean_ctor_set(v___x_1344_, 0, v___x_1349_);
v___x_1353_ = v___x_1344_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1348_);
v___x_1355_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_fields_1342_);
v___x_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
lean_inc(v___y_1347_);
v___x_1357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___y_1347_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = 0;
v___x_1359_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*1, v___x_1358_);
v___x_1360_ = l_Repr_addAppParen(v___x_1359_, v_prec_1325_);
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* v_x_1367_, lean_object* v_prec_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Syntax_instReprPreresolved_repr(v_x_1367_, v_prec_1368_);
lean_dec(v_prec_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_nat_to_int(v_a_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* v_a_1372_, lean_object* v_n_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(v_a_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* v_a_1375_, lean_object* v_n_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(v_a_1375_, v_n_1376_);
lean_dec(v_n_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l_Lean_Syntax_instReprPreresolved_repr(v___y_1380_, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_dec(v_x_1383_);
return v_x_1384_;
}
else
{
lean_object* v_head_1386_; lean_object* v_tail_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1398_; 
v_head_1386_ = lean_ctor_get(v_x_1385_, 0);
v_tail_1387_ = lean_ctor_get(v_x_1385_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1389_ = v_x_1385_;
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_tail_1387_);
lean_inc(v_head_1386_);
lean_dec(v_x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
lean_inc(v_x_1383_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 5);
lean_ctor_set(v___x_1389_, 1, v_x_1383_);
lean_ctor_set(v___x_1389_, 0, v_x_1384_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_x_1384_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_x_1383_);
v___x_1392_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1386_, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1392_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v_x_1384_ = v___x_1395_;
v_x_1385_ = v_tail_1387_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
lean_dec(v_x_1399_);
return v_x_1400_;
}
else
{
lean_object* v_head_1402_; lean_object* v_tail_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1414_; 
v_head_1402_ = lean_ctor_get(v_x_1401_, 0);
v_tail_1403_ = lean_ctor_get(v_x_1401_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1401_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1405_ = v_x_1401_;
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_tail_1403_);
lean_inc(v_head_1402_);
lean_dec(v_x_1401_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
lean_inc(v_x_1399_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 5);
lean_ctor_set(v___x_1405_, 1, v_x_1399_);
lean_ctor_set(v___x_1405_, 0, v_x_1400_);
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_x_1400_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_x_1399_);
v___x_1408_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = l_Lean_Syntax_instReprPreresolved_repr(v_head_1402_, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1408_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(v_x_1399_, v___x_1411_, v_tail_1403_);
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v___x_1417_; 
lean_dec(v_x_1416_);
v___x_1417_ = lean_box(0);
return v___x_1417_;
}
else
{
lean_object* v_tail_1418_; 
v_tail_1418_ = lean_ctor_get(v_x_1415_, 1);
if (lean_obj_tag(v_tail_1418_) == 0)
{
lean_object* v_head_1419_; lean_object* v___x_1420_; 
lean_dec(v_x_1416_);
v_head_1419_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_head_1419_);
lean_dec_ref_known(v_x_1415_, 2);
v___x_1420_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1419_);
return v___x_1420_;
}
else
{
lean_object* v_head_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_inc(v_tail_1418_);
v_head_1421_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_head_1421_);
lean_dec_ref_known(v_x_1415_, 2);
v___x_1422_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(v_head_1421_);
v___x_1423_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(v_x_1416_, v___x_1422_, v_tail_1418_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* v_a_1424_){
_start:
{
if (lean_obj_tag(v_a_1424_) == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1));
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1426_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1427_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(v_a_1424_, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8, &l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8_once, _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
v___x_1429_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9));
v___x_1430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1427_);
v___x_1431_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1428_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = 0;
v___x_1435_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set_uint8(v___x_1435_, sizeof(void*)*1, v___x_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_dec(v_x_1445_);
return v_x_1446_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
v_head_1448_ = lean_ctor_get(v_x_1447_, 0);
v_tail_1449_ = lean_ctor_get(v_x_1447_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_x_1447_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v_x_1447_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_tail_1449_);
lean_inc(v_head_1448_);
lean_dec(v_x_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
lean_inc(v_x_1445_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set_tag(v___x_1451_, 5);
lean_ctor_set(v___x_1451_, 1, v_x_1445_);
lean_ctor_set(v___x_1451_, 0, v_x_1446_);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_x_1446_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_x_1445_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = l_Lean_Syntax_instRepr_repr(v_head_1448_, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1454_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v_x_1446_ = v___x_1457_;
v_x_1447_ = v_tail_1449_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
if (lean_obj_tag(v_x_1463_) == 0)
{
lean_dec(v_x_1461_);
return v_x_1462_;
}
else
{
lean_object* v_head_1464_; lean_object* v_tail_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1476_; 
v_head_1464_ = lean_ctor_get(v_x_1463_, 0);
v_tail_1465_ = lean_ctor_get(v_x_1463_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1467_ = v_x_1463_;
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_tail_1465_);
lean_inc(v_head_1464_);
lean_dec(v_x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1476_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
lean_inc(v_x_1461_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 5);
lean_ctor_set(v___x_1467_, 1, v_x_1461_);
lean_ctor_set(v___x_1467_, 0, v_x_1462_);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_x_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_x_1461_);
v___x_1470_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = l_Lean_Syntax_instRepr_repr(v_head_1464_, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1470_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(v_x_1461_, v___x_1473_, v_tail_1465_);
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
lean_object* v___x_1479_; 
lean_dec(v_x_1478_);
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
else
{
lean_object* v_tail_1480_; 
v_tail_1480_ = lean_ctor_get(v_x_1477_, 1);
if (lean_obj_tag(v_tail_1480_) == 0)
{
lean_object* v_head_1481_; lean_object* v___x_1482_; 
lean_dec(v_x_1478_);
v_head_1481_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_head_1481_);
lean_dec_ref_known(v_x_1477_, 2);
v___x_1482_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1481_);
return v___x_1482_;
}
else
{
lean_object* v_head_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_inc(v_tail_1480_);
v_head_1483_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_head_1483_);
lean_dec_ref_known(v_x_1477_, 2);
v___x_1484_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(v_head_1483_);
v___x_1485_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(v_x_1478_, v___x_1484_, v_tail_1480_);
return v___x_1485_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0));
v___x_1488_ = lean_string_length(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
v___x_1490_ = lean_nat_to_int(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* v_xs_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = lean_array_get_size(v_xs_1496_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_nat_dec_eq(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1500_ = lean_array_to_list(v_xs_1496_);
v___x_1501_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5));
v___x_1502_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(v___x_1500_, v___x_1501_);
v___x_1503_ = lean_obj_once(&l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
v___x_1504_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3));
v___x_1505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1502_);
v___x_1506_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10));
v___x_1507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1503_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Std_Format_fill(v___x_1508_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; 
lean_dec_ref(v_xs_1496_);
v___x_1510_ = ((lean_object*)(l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5));
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* v_x_1524_, lean_object* v_prec_1525_){
_start:
{
lean_object* v___y_1527_; 
switch(lean_obj_tag(v_x_1524_))
{
case 0:
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = lean_unsigned_to_nat(1024u);
v___x_1534_ = lean_nat_dec_le(v___x_1533_, v_prec_1525_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1527_ = v___x_1535_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1527_ = v___x_1536_;
goto v___jp_1526_;
}
}
case 1:
{
lean_object* v_info_1537_; lean_object* v_kind_1538_; lean_object* v_args_1539_; lean_object* v___y_1541_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_info_1537_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_info_1537_);
v_kind_1538_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_kind_1538_);
v_args_1539_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_args_1539_);
lean_dec_ref_known(v_x_1524_, 3);
v___x_1557_ = lean_unsigned_to_nat(1024u);
v___x_1558_ = lean_nat_dec_le(v___x_1557_, v_prec_1525_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1541_ = v___x_1559_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1541_ = v___x_1560_;
goto v___jp_1540_;
}
v___jp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1542_ = lean_box(1);
v___x_1543_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__4));
v___x_1544_ = lean_unsigned_to_nat(1024u);
v___x_1545_ = l_instReprSourceInfo_repr(v_info_1537_, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1543_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1542_);
v___x_1548_ = l_Lean_Name_reprPrec(v_kind_1538_, v___x_1544_);
v___x_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1542_);
v___x_1551_ = l_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(v_args_1539_);
v___x_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
lean_inc(v___y_1541_);
v___x_1553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___y_1541_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = 0;
v___x_1555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*1, v___x_1554_);
v___x_1556_ = l_Repr_addAppParen(v___x_1555_, v_prec_1525_);
return v___x_1556_;
}
}
case 2:
{
lean_object* v_info_1561_; lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1587_; 
v_info_1561_ = lean_ctor_get(v_x_1524_, 0);
v_val_1562_ = lean_ctor_get(v_x_1524_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_x_1524_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1564_ = v_x_1524_;
v_isShared_1565_ = v_isSharedCheck_1587_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_inc(v_info_1561_);
lean_dec(v_x_1524_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1587_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___y_1567_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_unsigned_to_nat(1024u);
v___x_1584_ = lean_nat_dec_le(v___x_1583_, v_prec_1525_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1567_ = v___x_1585_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1567_ = v___x_1586_;
goto v___jp_1566_;
}
v___jp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1568_ = lean_box(1);
v___x_1569_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__7));
v___x_1570_ = lean_unsigned_to_nat(1024u);
v___x_1571_ = l_instReprSourceInfo_repr(v_info_1561_, v___x_1570_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 5);
lean_ctor_set(v___x_1564_, 1, v___x_1571_);
lean_ctor_set(v___x_1564_, 0, v___x_1569_);
v___x_1573_ = v___x_1564_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___x_1568_);
v___x_1575_ = l_String_quote(v_val_1562_);
v___x_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1574_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
lean_inc(v___y_1567_);
v___x_1578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1567_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = 0;
v___x_1580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*1, v___x_1579_);
v___x_1581_ = l_Repr_addAppParen(v___x_1580_, v_prec_1525_);
return v___x_1581_;
}
}
}
}
default: 
{
lean_object* v_info_1588_; lean_object* v_rawVal_1589_; lean_object* v_val_1590_; lean_object* v_preresolved_1591_; lean_object* v___y_1593_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_info_1588_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_info_1588_);
v_rawVal_1589_ = lean_ctor_get(v_x_1524_, 1);
lean_inc_ref(v_rawVal_1589_);
v_val_1590_ = lean_ctor_get(v_x_1524_, 2);
lean_inc(v_val_1590_);
v_preresolved_1591_ = lean_ctor_get(v_x_1524_, 3);
lean_inc(v_preresolved_1591_);
lean_dec_ref_known(v_x_1524_, 4);
v___x_1616_ = lean_unsigned_to_nat(1024u);
v___x_1617_ = lean_nat_dec_le(v___x_1616_, v_prec_1525_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_1593_ = v___x_1618_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_1593_ = v___x_1619_;
goto v___jp_1592_;
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1594_ = lean_box(1);
v___x_1595_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__10));
v___x_1596_ = lean_unsigned_to_nat(1024u);
v___x_1597_ = l_instReprSourceInfo_repr(v_info_1588_, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1595_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___x_1594_);
v___x_1600_ = lean_substring_tostring(v_rawVal_1589_);
v___x_1601_ = l_String_quote(v___x_1600_);
v___x_1602_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__11));
v___x_1603_ = lean_string_append(v___x_1601_, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1599_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1594_);
v___x_1607_ = l_Lean_Name_reprPrec(v_val_1590_, v___x_1596_);
v___x_1608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___x_1594_);
v___x_1610_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_preresolved_1591_);
v___x_1611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
lean_inc(v___y_1593_);
v___x_1612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1593_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = 0;
v___x_1614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set_uint8(v___x_1614_, sizeof(void*)*1, v___x_1613_);
v___x_1615_ = l_Repr_addAppParen(v___x_1614_, v_prec_1525_);
return v___x_1615_;
}
}
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = ((lean_object*)(l_Lean_Syntax_instRepr_repr___closed__1));
lean_inc(v___y_1527_);
v___x_1529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___y_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = 0;
v___x_1531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*1, v___x_1530_);
v___x_1532_ = l_Repr_addAppParen(v___x_1531_, v_prec_1525_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = l_Lean_Syntax_instRepr_repr(v___y_1620_, v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* v_x_1623_, lean_object* v_prec_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Syntax_instRepr_repr(v_x_1623_, v_prec_1624_);
lean_dec(v_prec_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* v_a_1626_, lean_object* v_n_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(v_a_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* v_a_1629_, lean_object* v_n_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(v_a_1629_, v_n_1630_);
lean_dec(v_n_1630_);
return v_res_1631_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_unsigned_to_nat(7u);
v___x_1648_ = lean_nat_to_int(v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0));
v___x_1651_ = lean_string_length(v___x_1650_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
v___x_1653_ = lean_nat_to_int(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* v_x_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1659_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6));
v___x_1660_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = l_Lean_Syntax_instRepr_repr(v_x_1658_, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1660_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = 0;
v___x_1665_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*1, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1659_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_1668_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_1669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v___x_1666_);
v___x_1670_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_1671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1667_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*1, v___x_1664_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* v_ks_1674_, lean_object* v_x_1675_, lean_object* v_prec_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_x_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* v_ks_1678_, lean_object* v_x_1679_, lean_object* v_prec_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Syntax_instReprTSyntax_repr(v_ks_1678_, v_x_1679_, v_prec_1680_);
lean_dec(v_prec_1680_);
lean_dec(v_ks_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* v_ks_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(v___x_1683_, 0, v_ks_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(lean_object* v_stx_1684_){
_start:
{
lean_inc(v_stx_1684_);
return v_stx_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed(lean_object* v_stx_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(v_stx_1685_);
lean_dec(v_stx_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* v_k_1688_, lean_object* v_ks_1689_){
_start:
{
lean_object* v___f_1690_; 
v___f_1690_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0));
return v___f_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* v_k_1691_, lean_object* v_ks_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(v_k_1691_, v_ks_1692_);
lean_dec(v_ks_1692_);
lean_dec(v_k_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* v_ks_1694_, lean_object* v_k_x27_1695_){
_start:
{
lean_object* v___f_1696_; 
v___f_1696_ = ((lean_object*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0));
return v___f_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* v_ks_1697_, lean_object* v_k_x27_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(v_ks_1697_, v_k_x27_1698_);
lean_dec(v_k_x27_1698_);
lean_dec(v_ks_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* v_s_1700_){
_start:
{
lean_inc(v_s_1700_);
return v_s_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* v_s_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_TSyntax_instCoeIdentTerm___lam__0(v_s_1701_);
lean_dec(v_s_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* v_info_1705_, lean_object* v_ss_1706_, lean_object* v_n_1707_, lean_object* v_res_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1709_, 0, v_info_1705_);
lean_ctor_set(v___x_1709_, 1, v_ss_1706_);
lean_ctor_set(v___x_1709_, 2, v_n_1707_);
lean_ctor_set(v___x_1709_, 3, v_res_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* v_k_1718_){
_start:
{
lean_object* v___f_1719_; 
v___f_1719_ = ((lean_object*)(l_Lean_TSyntax_instCoeIdentTerm___closed__0));
return v___f_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* v_k_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_TSyntax_Compat_instCoeTailSyntax(v_k_1720_);
lean_dec(v_k_1720_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* v_k_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(v___x_1723_, 0, v_k_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
if (lean_obj_tag(v_x_1724_) == 0)
{
if (lean_obj_tag(v_x_1725_) == 0)
{
uint8_t v___x_1726_; 
v___x_1726_ = 1;
return v___x_1726_;
}
else
{
uint8_t v___x_1727_; 
v___x_1727_ = 0;
return v___x_1727_;
}
}
else
{
if (lean_obj_tag(v_x_1725_) == 0)
{
uint8_t v___x_1728_; 
v___x_1728_ = 0;
return v___x_1728_;
}
else
{
lean_object* v_head_1729_; lean_object* v_tail_1730_; lean_object* v_head_1731_; lean_object* v_tail_1732_; uint8_t v___x_1733_; 
v_head_1729_ = lean_ctor_get(v_x_1724_, 0);
v_tail_1730_ = lean_ctor_get(v_x_1724_, 1);
v_head_1731_ = lean_ctor_get(v_x_1725_, 0);
v_tail_1732_ = lean_ctor_get(v_x_1725_, 1);
v___x_1733_ = lean_string_dec_eq(v_head_1729_, v_head_1731_);
if (v___x_1733_ == 0)
{
return v___x_1733_;
}
else
{
v_x_1724_ = v_tail_1730_;
v_x_1725_ = v_tail_1732_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_x_1735_, v_x_1736_);
lean_dec(v_x_1736_);
lean_dec(v_x_1735_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* v_x_1739_, lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1739_) == 0)
{
if (lean_obj_tag(v_x_1740_) == 0)
{
lean_object* v_ns_1741_; lean_object* v_ns_1742_; uint8_t v___x_1743_; 
v_ns_1741_ = lean_ctor_get(v_x_1739_, 0);
v_ns_1742_ = lean_ctor_get(v_x_1740_, 0);
v___x_1743_ = lean_name_eq(v_ns_1741_, v_ns_1742_);
return v___x_1743_;
}
else
{
uint8_t v___x_1744_; 
v___x_1744_ = 0;
return v___x_1744_;
}
}
else
{
if (lean_obj_tag(v_x_1740_) == 1)
{
lean_object* v_n_1745_; lean_object* v_fields_1746_; lean_object* v_n_1747_; lean_object* v_fields_1748_; uint8_t v___x_1749_; 
v_n_1745_ = lean_ctor_get(v_x_1739_, 0);
v_fields_1746_ = lean_ctor_get(v_x_1739_, 1);
v_n_1747_ = lean_ctor_get(v_x_1740_, 0);
v_fields_1748_ = lean_ctor_get(v_x_1740_, 1);
v___x_1749_ = lean_name_eq(v_n_1745_, v_n_1747_);
if (v___x_1749_ == 0)
{
return v___x_1749_;
}
else
{
uint8_t v___x_1750_; 
v___x_1750_ = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(v_fields_1746_, v_fields_1748_);
return v___x_1750_;
}
}
else
{
uint8_t v___x_1751_; 
v___x_1751_ = 0;
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
uint8_t v_res_1754_; lean_object* v_r_1755_; 
v_res_1754_ = l_Lean_Syntax_instBEqPreresolved_beq(v_x_1752_, v_x_1753_);
lean_dec_ref(v_x_1753_);
lean_dec_ref(v_x_1752_);
v_r_1755_ = lean_box(v_res_1754_);
return v_r_1755_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 0)
{
if (lean_obj_tag(v_x_1759_) == 0)
{
uint8_t v___x_1760_; 
v___x_1760_ = 1;
return v___x_1760_;
}
else
{
uint8_t v___x_1761_; 
v___x_1761_ = 0;
return v___x_1761_;
}
}
else
{
if (lean_obj_tag(v_x_1759_) == 0)
{
uint8_t v___x_1762_; 
v___x_1762_ = 0;
return v___x_1762_;
}
else
{
lean_object* v_head_1763_; lean_object* v_tail_1764_; lean_object* v_head_1765_; lean_object* v_tail_1766_; uint8_t v___x_1767_; 
v_head_1763_ = lean_ctor_get(v_x_1758_, 0);
v_tail_1764_ = lean_ctor_get(v_x_1758_, 1);
v_head_1765_ = lean_ctor_get(v_x_1759_, 0);
v_tail_1766_ = lean_ctor_get(v_x_1759_, 1);
v___x_1767_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_1763_, v_head_1765_);
if (v___x_1767_ == 0)
{
return v___x_1767_;
}
else
{
v_x_1758_ = v_tail_1764_;
v_x_1759_ = v_tail_1766_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
uint8_t v_res_1771_; lean_object* v_r_1772_; 
v_res_1771_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_x_1769_, v_x_1770_);
lean_dec(v_x_1770_);
lean_dec(v_x_1769_);
v_r_1772_ = lean_box(v_res_1771_);
return v_r_1772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* v_x_1773_, lean_object* v_x_1774_){
_start:
{
switch(lean_obj_tag(v_x_1773_))
{
case 0:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
uint8_t v___x_1775_; 
v___x_1775_ = 1;
return v___x_1775_;
}
else
{
uint8_t v___x_1776_; 
v___x_1776_ = 0;
return v___x_1776_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1774_) == 1)
{
lean_object* v_kind_1777_; lean_object* v_args_1778_; lean_object* v_kind_1779_; lean_object* v_args_1780_; uint8_t v___x_1781_; 
v_kind_1777_ = lean_ctor_get(v_x_1773_, 1);
v_args_1778_ = lean_ctor_get(v_x_1773_, 2);
v_kind_1779_ = lean_ctor_get(v_x_1774_, 1);
v_args_1780_ = lean_ctor_get(v_x_1774_, 2);
v___x_1781_ = lean_name_eq(v_kind_1777_, v_kind_1779_);
if (v___x_1781_ == 0)
{
return v___x_1781_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_array_get_size(v_args_1778_);
v___x_1783_ = lean_array_get_size(v_args_1780_);
v___x_1784_ = lean_nat_dec_eq(v___x_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
return v___x_1784_;
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_args_1778_, v_args_1780_, v___x_1782_);
return v___x_1785_;
}
}
}
else
{
uint8_t v___x_1786_; 
v___x_1786_ = 0;
return v___x_1786_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1774_) == 2)
{
lean_object* v_val_1787_; lean_object* v_val_1788_; uint8_t v___x_1789_; 
v_val_1787_ = lean_ctor_get(v_x_1773_, 1);
v_val_1788_ = lean_ctor_get(v_x_1774_, 1);
v___x_1789_ = lean_string_dec_eq(v_val_1787_, v_val_1788_);
return v___x_1789_;
}
else
{
uint8_t v___x_1790_; 
v___x_1790_ = 0;
return v___x_1790_;
}
}
default: 
{
if (lean_obj_tag(v_x_1774_) == 3)
{
lean_object* v_rawVal_1791_; lean_object* v_val_1792_; lean_object* v_preresolved_1793_; lean_object* v_rawVal_1794_; lean_object* v_val_1795_; lean_object* v_preresolved_1796_; uint8_t v___y_1798_; uint8_t v___x_1800_; 
v_rawVal_1791_ = lean_ctor_get(v_x_1773_, 1);
v_val_1792_ = lean_ctor_get(v_x_1773_, 2);
v_preresolved_1793_ = lean_ctor_get(v_x_1773_, 3);
v_rawVal_1794_ = lean_ctor_get(v_x_1774_, 1);
v_val_1795_ = lean_ctor_get(v_x_1774_, 2);
v_preresolved_1796_ = lean_ctor_get(v_x_1774_, 3);
lean_inc_ref(v_rawVal_1794_);
lean_inc_ref(v_rawVal_1791_);
v___x_1800_ = lean_substring_beq(v_rawVal_1791_, v_rawVal_1794_);
if (v___x_1800_ == 0)
{
v___y_1798_ = v___x_1800_;
goto v___jp_1797_;
}
else
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_name_eq(v_val_1792_, v_val_1795_);
v___y_1798_ = v___x_1801_;
goto v___jp_1797_;
}
v___jp_1797_:
{
if (v___y_1798_ == 0)
{
return v___y_1798_;
}
else
{
uint8_t v___x_1799_; 
v___x_1799_ = l_List_beq___at___00Lean_Syntax_structEq_spec__1(v_preresolved_1793_, v_preresolved_1796_);
return v___x_1799_;
}
}
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = 0;
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* v_xs_1803_, lean_object* v_ys_1804_, lean_object* v_x_1805_){
_start:
{
lean_object* v_zero_1806_; uint8_t v_isZero_1807_; 
v_zero_1806_ = lean_unsigned_to_nat(0u);
v_isZero_1807_ = lean_nat_dec_eq(v_x_1805_, v_zero_1806_);
if (v_isZero_1807_ == 1)
{
lean_dec(v_x_1805_);
return v_isZero_1807_;
}
else
{
lean_object* v_one_1808_; lean_object* v_n_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_one_1808_ = lean_unsigned_to_nat(1u);
v_n_1809_ = lean_nat_sub(v_x_1805_, v_one_1808_);
lean_dec(v_x_1805_);
v___x_1810_ = lean_array_fget_borrowed(v_xs_1803_, v_n_1809_);
v___x_1811_ = lean_array_fget_borrowed(v_ys_1804_, v_n_1809_);
v___x_1812_ = l_Lean_Syntax_structEq(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_dec(v_n_1809_);
return v___x_1812_;
}
else
{
v_x_1805_ = v_n_1809_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* v_xs_1814_, lean_object* v_ys_1815_, lean_object* v_x_1816_){
_start:
{
uint8_t v_res_1817_; lean_object* v_r_1818_; 
v_res_1817_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1814_, v_ys_1815_, v_x_1816_);
lean_dec_ref(v_ys_1815_);
lean_dec_ref(v_xs_1814_);
v_r_1818_ = lean_box(v_res_1817_);
return v_r_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
uint8_t v_res_1821_; lean_object* v_r_1822_; 
v_res_1821_ = l_Lean_Syntax_structEq(v_x_1819_, v_x_1820_);
lean_dec(v_x_1820_);
lean_dec(v_x_1819_);
v_r_1822_ = lean_box(v_res_1821_);
return v_r_1822_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* v_xs_1823_, lean_object* v_ys_1824_, lean_object* v_hsz_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(v_xs_1823_, v_ys_1824_, v_x_1826_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* v_xs_1829_, lean_object* v_ys_1830_, lean_object* v_hsz_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(v_xs_1829_, v_ys_1830_, v_hsz_1831_, v_x_1832_, v_x_1833_);
lean_dec_ref(v_ys_1830_);
lean_dec_ref(v_xs_1829_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* v_k_1839_){
_start:
{
lean_object* v___f_1840_; 
v___f_1840_ = ((lean_object*)(l_Lean_Syntax_instBEqTSyntax___closed__0));
return v___f_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* v_k_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Syntax_instBEqTSyntax(v_k_1841_);
lean_dec(v_k_1841_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* v_as_1843_, lean_object* v_i_1844_){
_start:
{
lean_object* v_zero_1845_; uint8_t v_isZero_1846_; 
v_zero_1845_ = lean_unsigned_to_nat(0u);
v_isZero_1846_ = lean_nat_dec_eq(v_i_1844_, v_zero_1845_);
if (v_isZero_1846_ == 1)
{
lean_object* v___x_1847_; 
lean_dec(v_i_1844_);
v___x_1847_ = lean_box(0);
return v___x_1847_;
}
else
{
lean_object* v_one_1848_; lean_object* v_n_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_one_1848_ = lean_unsigned_to_nat(1u);
v_n_1849_ = lean_nat_sub(v_i_1844_, v_one_1848_);
lean_dec(v_i_1844_);
v___x_1850_ = lean_array_fget_borrowed(v_as_1843_, v_n_1849_);
v___x_1851_ = l_Lean_Syntax_getTailInfo_x3f(v___x_1850_);
if (lean_obj_tag(v___x_1851_) == 0)
{
v_i_1844_ = v_n_1849_;
goto _start;
}
else
{
lean_dec(v_n_1849_);
return v___x_1851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* v_x_1853_){
_start:
{
switch(lean_obj_tag(v_x_1853_))
{
case 2:
{
lean_object* v_info_1854_; lean_object* v___x_1855_; 
v_info_1854_ = lean_ctor_get(v_x_1853_, 0);
lean_inc(v_info_1854_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_info_1854_);
return v___x_1855_;
}
case 3:
{
lean_object* v_info_1856_; lean_object* v___x_1857_; 
v_info_1856_ = lean_ctor_get(v_x_1853_, 0);
lean_inc(v_info_1856_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_info_1856_);
return v___x_1857_;
}
case 1:
{
lean_object* v_info_1858_; 
v_info_1858_ = lean_ctor_get(v_x_1853_, 0);
if (lean_obj_tag(v_info_1858_) == 2)
{
lean_object* v_args_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_args_1859_ = lean_ctor_get(v_x_1853_, 2);
v___x_1860_ = lean_array_get_size(v_args_1859_);
v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_args_1859_, v___x_1860_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; 
lean_inc(v_info_1858_);
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_info_1858_);
return v___x_1862_;
}
}
default: 
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_box(0);
return v___x_1863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* v_x_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_Syntax_getTailInfo_x3f(v_x_1864_);
lean_dec(v_x_1864_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* v_as_1866_, lean_object* v_i_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1866_, v_i_1867_);
lean_dec_ref(v_as_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* v_as_1869_, lean_object* v_i_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(v_as_1869_, v_i_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* v_as_1873_, lean_object* v_i_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(v_as_1873_, v_i_1874_, v_a_1875_);
lean_dec_ref(v_as_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* v_stx_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1877_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_box(2);
return v___x_1879_;
}
else
{
lean_object* v_val_1880_; 
v_val_1880_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v___x_1878_, 1);
return v_val_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* v_stx_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Syntax_getTailInfo(v_stx_1881_);
lean_dec(v_stx_1881_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* v_stx_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_1883_);
if (lean_obj_tag(v___x_1884_) == 1)
{
lean_object* v_val_1885_; 
v_val_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v___x_1884_, 1);
if (lean_obj_tag(v_val_1885_) == 0)
{
lean_object* v_trailing_1886_; lean_object* v_startPos_1887_; lean_object* v_stopPos_1888_; lean_object* v___x_1889_; 
v_trailing_1886_ = lean_ctor_get(v_val_1885_, 2);
lean_inc_ref(v_trailing_1886_);
lean_dec_ref_known(v_val_1885_, 4);
v_startPos_1887_ = lean_ctor_get(v_trailing_1886_, 1);
lean_inc(v_startPos_1887_);
v_stopPos_1888_ = lean_ctor_get(v_trailing_1886_, 2);
lean_inc(v_stopPos_1888_);
lean_dec_ref(v_trailing_1886_);
v___x_1889_ = lean_nat_sub(v_stopPos_1888_, v_startPos_1887_);
lean_dec(v_startPos_1887_);
lean_dec(v_stopPos_1888_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; 
lean_dec(v_val_1885_);
v___x_1890_ = lean_unsigned_to_nat(0u);
return v___x_1890_;
}
}
else
{
lean_object* v___x_1891_; 
lean_dec(v___x_1884_);
v___x_1891_ = lean_unsigned_to_nat(0u);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* v_stx_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Syntax_getTrailingSize(v_stx_1892_);
lean_dec(v_stx_1892_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* v_stx_1894_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = l_Lean_Syntax_getTailInfo(v_stx_1894_);
v___x_1896_ = l_Lean_SourceInfo_getTrailing_x3f(v___x_1895_);
lean_dec(v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* v_stx_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Syntax_getTrailing_x3f(v_stx_1897_);
lean_dec(v_stx_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* v_stx_1899_, uint8_t v_canonicalOnly_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = l_Lean_Syntax_getTailInfo(v_stx_1899_);
v___x_1902_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v___x_1901_, v_canonicalOnly_1900_);
lean_dec(v___x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* v_stx_1903_, lean_object* v_canonicalOnly_1904_){
_start:
{
uint8_t v_canonicalOnly_boxed_1905_; lean_object* v_res_1906_; 
v_canonicalOnly_boxed_1905_ = lean_unbox(v_canonicalOnly_1904_);
v_res_1906_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1903_, v_canonicalOnly_boxed_1905_);
lean_dec(v_stx_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* v_stx_1907_, uint8_t v_withLeading_1908_, uint8_t v_withTrailing_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_Syntax_getHeadInfo(v_stx_1907_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_leading_1911_; lean_object* v_pos_1912_; lean_object* v___x_1913_; 
v_leading_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc_ref(v_leading_1911_);
v_pos_1912_ = lean_ctor_get(v___x_1910_, 1);
lean_inc(v_pos_1912_);
lean_dec_ref_known(v___x_1910_, 4);
v___x_1913_ = l_Lean_Syntax_getTailInfo(v_stx_1907_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_trailing_1914_; lean_object* v_endPos_1915_; lean_object* v_str_1916_; lean_object* v_startPos_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1931_; 
v_trailing_1914_ = lean_ctor_get(v___x_1913_, 2);
lean_inc_ref(v_trailing_1914_);
v_endPos_1915_ = lean_ctor_get(v___x_1913_, 3);
lean_inc(v_endPos_1915_);
lean_dec_ref_known(v___x_1913_, 4);
v_str_1916_ = lean_ctor_get(v_leading_1911_, 0);
v_startPos_1917_ = lean_ctor_get(v_leading_1911_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_leading_1911_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_leading_1911_, 2);
lean_dec(v_unused_1932_);
v___x_1919_ = v_leading_1911_;
v_isShared_1920_ = v_isSharedCheck_1931_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_startPos_1917_);
lean_inc(v_str_1916_);
lean_dec(v_leading_1911_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1931_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1929_; 
if (v_withLeading_1908_ == 0)
{
lean_dec(v_startPos_1917_);
v___y_1929_ = v_pos_1912_;
goto v___jp_1928_;
}
else
{
lean_dec(v_pos_1912_);
v___y_1929_ = v_startPos_1917_;
goto v___jp_1928_;
}
v___jp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 2, v___y_1923_);
lean_ctor_set(v___x_1919_, 1, v___y_1922_);
v___x_1925_ = v___x_1919_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_str_1916_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___y_1922_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v___y_1923_);
v___x_1925_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
v___jp_1928_:
{
if (v_withTrailing_1909_ == 0)
{
lean_dec_ref(v_trailing_1914_);
v___y_1922_ = v___y_1929_;
v___y_1923_ = v_endPos_1915_;
goto v___jp_1921_;
}
else
{
lean_object* v_stopPos_1930_; 
lean_dec(v_endPos_1915_);
v_stopPos_1930_ = lean_ctor_get(v_trailing_1914_, 2);
lean_inc(v_stopPos_1930_);
lean_dec_ref(v_trailing_1914_);
v___y_1922_ = v___y_1929_;
v___y_1923_ = v_stopPos_1930_;
goto v___jp_1921_;
}
}
}
}
else
{
lean_object* v___x_1933_; 
lean_dec(v___x_1913_);
lean_dec(v_pos_1912_);
lean_dec_ref(v_leading_1911_);
v___x_1933_ = lean_box(0);
return v___x_1933_;
}
}
else
{
lean_object* v___x_1934_; 
lean_dec(v___x_1910_);
v___x_1934_ = lean_box(0);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* v_stx_1935_, lean_object* v_withLeading_1936_, lean_object* v_withTrailing_1937_){
_start:
{
uint8_t v_withLeading_boxed_1938_; uint8_t v_withTrailing_boxed_1939_; lean_object* v_res_1940_; 
v_withLeading_boxed_1938_ = lean_unbox(v_withLeading_1936_);
v_withTrailing_boxed_1939_ = lean_unbox(v_withTrailing_1937_);
v_res_1940_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1935_, v_withLeading_boxed_1938_, v_withTrailing_boxed_1939_);
lean_dec(v_stx_1935_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* v_a_1941_, lean_object* v_f_1942_, lean_object* v_i_1943_){
_start:
{
lean_object* v_zero_1944_; uint8_t v_isZero_1945_; 
v_zero_1944_ = lean_unsigned_to_nat(0u);
v_isZero_1945_ = lean_nat_dec_eq(v_i_1943_, v_zero_1944_);
if (v_isZero_1945_ == 1)
{
lean_object* v___x_1946_; 
lean_dec(v_i_1943_);
lean_dec_ref(v_f_1942_);
lean_dec_ref(v_a_1941_);
v___x_1946_ = lean_box(0);
return v___x_1946_;
}
else
{
lean_object* v_one_1947_; lean_object* v_n_1948_; lean_object* v_v_1949_; lean_object* v___x_1950_; 
v_one_1947_ = lean_unsigned_to_nat(1u);
v_n_1948_ = lean_nat_sub(v_i_1943_, v_one_1947_);
lean_dec(v_i_1943_);
v_v_1949_ = lean_array_fget_borrowed(v_a_1941_, v_n_1948_);
lean_inc_ref(v_f_1942_);
lean_inc(v_v_1949_);
v___x_1950_ = lean_apply_1(v_f_1942_, v_v_1949_);
if (lean_obj_tag(v___x_1950_) == 0)
{
v_i_1943_ = v_n_1948_;
goto _start;
}
else
{
lean_object* v_val_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_f_1942_);
v_val_1952_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v___x_1950_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_val_1952_);
lean_dec(v___x_1950_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = lean_array_fset(v_a_1941_, v_n_1948_, v_val_1952_);
lean_dec(v_n_1948_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* v_00_u03b1_1961_, lean_object* v_a_1962_, lean_object* v_f_1963_, lean_object* v_i_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(v_a_1962_, v_f_1963_, v_i_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* v_info_1966_, lean_object* v_x_1967_){
_start:
{
switch(lean_obj_tag(v_x_1967_))
{
case 2:
{
lean_object* v_val_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
v_val_1968_ = lean_ctor_get(v_x_1967_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1967_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_x_1967_, 0);
lean_dec(v_unused_1977_);
v___x_1970_ = v_x_1967_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_val_1968_);
lean_dec(v_x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_info_1966_);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_info_1966_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_val_1968_);
v___x_1973_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
}
}
case 3:
{
lean_object* v_rawVal_1978_; lean_object* v_val_1979_; lean_object* v_preresolved_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
v_rawVal_1978_ = lean_ctor_get(v_x_1967_, 1);
v_val_1979_ = lean_ctor_get(v_x_1967_, 2);
v_preresolved_1980_ = lean_ctor_get(v_x_1967_, 3);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_x_1967_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v_x_1967_, 0);
lean_dec(v_unused_1989_);
v___x_1982_ = v_x_1967_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_preresolved_1980_);
lean_inc(v_val_1979_);
lean_inc(v_rawVal_1978_);
lean_dec(v_x_1967_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_info_1966_);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_info_1966_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_rawVal_1978_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_val_1979_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_preresolved_1980_);
v___x_1985_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
}
case 1:
{
lean_object* v_info_1990_; lean_object* v_kind_1991_; lean_object* v_args_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2010_; 
v_info_1990_ = lean_ctor_get(v_x_1967_, 0);
v_kind_1991_ = lean_ctor_get(v_x_1967_, 1);
v_args_1992_ = lean_ctor_get(v_x_1967_, 2);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_x_1967_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1994_ = v_x_1967_;
v_isShared_1995_ = v_isSharedCheck_2010_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_args_1992_);
lean_inc(v_kind_1991_);
lean_inc(v_info_1990_);
lean_dec(v_x_1967_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2010_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_array_get_size(v_args_1992_);
v___x_1997_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(v_info_1966_, v_args_1992_, v___x_1996_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1998_; 
lean_del_object(v___x_1994_);
lean_dec(v_kind_1991_);
lean_dec(v_info_1990_);
v___x_1998_ = lean_box(0);
return v___x_1998_;
}
else
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2009_; 
v_val_1999_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2001_ = v___x_1997_;
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v___x_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 2, v_val_1999_);
v___x_2004_ = v___x_1994_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_info_1990_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_kind_1991_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_val_1999_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2011_; 
lean_dec(v_x_1967_);
lean_dec(v_info_1966_);
v___x_2011_ = lean_box(0);
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* v_info_2012_, lean_object* v_a_2013_, lean_object* v_i_2014_){
_start:
{
lean_object* v_zero_2015_; uint8_t v_isZero_2016_; 
v_zero_2015_ = lean_unsigned_to_nat(0u);
v_isZero_2016_ = lean_nat_dec_eq(v_i_2014_, v_zero_2015_);
if (v_isZero_2016_ == 1)
{
lean_object* v___x_2017_; 
lean_dec(v_i_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_info_2012_);
v___x_2017_ = lean_box(0);
return v___x_2017_;
}
else
{
lean_object* v_one_2018_; lean_object* v_n_2019_; lean_object* v_v_2020_; lean_object* v___x_2021_; 
v_one_2018_ = lean_unsigned_to_nat(1u);
v_n_2019_ = lean_nat_sub(v_i_2014_, v_one_2018_);
lean_dec(v_i_2014_);
v_v_2020_ = lean_array_fget_borrowed(v_a_2013_, v_n_2019_);
lean_inc(v_v_2020_);
lean_inc(v_info_2012_);
v___x_2021_ = l_Lean_Syntax_setTailInfoAux(v_info_2012_, v_v_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
v_i_2014_ = v_n_2019_;
goto _start;
}
else
{
lean_object* v_val_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_info_2012_);
v_val_2023_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2025_ = v___x_2021_;
v_isShared_2026_ = v_isSharedCheck_2031_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_val_2023_);
lean_dec(v___x_2021_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2031_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_array_fset(v_a_2013_, v_n_2019_, v_val_2023_);
lean_dec(v_n_2019_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2027_);
v___x_2029_ = v___x_2025_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* v_stx_2032_, lean_object* v_info_2033_){
_start:
{
lean_object* v___x_2034_; 
lean_inc(v_stx_2032_);
v___x_2034_ = l_Lean_Syntax_setTailInfoAux(v_info_2033_, v_stx_2032_);
if (lean_obj_tag(v___x_2034_) == 0)
{
return v_stx_2032_;
}
else
{
lean_object* v_val_2035_; 
lean_dec(v_stx_2032_);
v_val_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_val_2035_);
lean_dec_ref_known(v___x_2034_, 1);
return v_val_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* v_stx_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_Syntax_getTailInfo(v_stx_2036_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_trailing_2038_; lean_object* v_leading_2039_; lean_object* v_pos_2040_; lean_object* v_endPos_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2059_; 
v_trailing_2038_ = lean_ctor_get(v___x_2037_, 2);
v_leading_2039_ = lean_ctor_get(v___x_2037_, 0);
v_pos_2040_ = lean_ctor_get(v___x_2037_, 1);
v_endPos_2041_ = lean_ctor_get(v___x_2037_, 3);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2043_ = v___x_2037_;
v_isShared_2044_ = v_isSharedCheck_2059_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_endPos_2041_);
lean_inc(v_trailing_2038_);
lean_inc(v_pos_2040_);
lean_inc(v_leading_2039_);
lean_dec(v___x_2037_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2059_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_str_2045_; lean_object* v_startPos_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2057_; 
v_str_2045_ = lean_ctor_get(v_trailing_2038_, 0);
v_startPos_2046_ = lean_ctor_get(v_trailing_2038_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_trailing_2038_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_trailing_2038_, 2);
lean_dec(v_unused_2058_);
v___x_2048_ = v_trailing_2038_;
v_isShared_2049_ = v_isSharedCheck_2057_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_startPos_2046_);
lean_inc(v_str_2045_);
lean_dec(v_trailing_2038_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2057_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
lean_inc(v_startPos_2046_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 2, v_startPos_2046_);
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_str_2045_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_startPos_2046_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_startPos_2046_);
v___x_2051_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2053_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 2, v___x_2051_);
v___x_2053_ = v___x_2043_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_leading_2039_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_pos_2040_);
lean_ctor_set(v_reuseFailAlloc_2055_, 2, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_endPos_2041_);
v___x_2053_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_Syntax_setTailInfo(v_stx_2036_, v___x_2053_);
return v___x_2054_;
}
}
}
}
}
else
{
lean_dec(v___x_2037_);
return v_stx_2036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* v_a_2060_, lean_object* v_f_2061_, lean_object* v_i_2062_){
_start:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = lean_array_get_size(v_a_2060_);
v___x_2064_ = lean_nat_dec_lt(v_i_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; 
lean_dec(v_i_2062_);
lean_dec_ref(v_f_2061_);
lean_dec_ref(v_a_2060_);
v___x_2065_ = lean_box(0);
return v___x_2065_;
}
else
{
lean_object* v_v_2066_; lean_object* v___x_2067_; 
v_v_2066_ = lean_array_fget_borrowed(v_a_2060_, v_i_2062_);
lean_inc_ref(v_f_2061_);
lean_inc(v_v_2066_);
v___x_2067_ = lean_apply_1(v_f_2061_, v_v_2066_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_add(v_i_2062_, v___x_2068_);
lean_dec(v_i_2062_);
v_i_2062_ = v___x_2069_;
goto _start;
}
else
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_f_2061_);
v_val_2071_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2073_ = v___x_2067_;
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v___x_2067_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_array_fset(v_a_2060_, v_i_2062_, v_val_2071_);
lean_dec(v_i_2062_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2075_);
v___x_2077_ = v___x_2073_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* v_00_u03b1_2080_, lean_object* v_inst_2081_, lean_object* v_a_2082_, lean_object* v_f_2083_, lean_object* v_i_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(v_a_2082_, v_f_2083_, v_i_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* v_00_u03b1_2086_, lean_object* v_inst_2087_, lean_object* v_a_2088_, lean_object* v_f_2089_, lean_object* v_i_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(v_00_u03b1_2086_, v_inst_2087_, v_a_2088_, v_f_2089_, v_i_2090_);
lean_dec(v_inst_2087_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* v_info_2092_, lean_object* v_x_2093_){
_start:
{
switch(lean_obj_tag(v_x_2093_))
{
case 2:
{
lean_object* v_val_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2102_; 
v_val_2094_ = lean_ctor_get(v_x_2093_, 1);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; 
v_unused_2103_ = lean_ctor_get(v_x_2093_, 0);
lean_dec(v_unused_2103_);
v___x_2096_ = v_x_2093_;
v_isShared_2097_ = v_isSharedCheck_2102_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_val_2094_);
lean_dec(v_x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2102_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v_info_2092_);
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_info_2092_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_val_2094_);
v___x_2099_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
}
case 3:
{
lean_object* v_rawVal_2104_; lean_object* v_val_2105_; lean_object* v_preresolved_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2114_; 
v_rawVal_2104_ = lean_ctor_get(v_x_2093_, 1);
v_val_2105_ = lean_ctor_get(v_x_2093_, 2);
v_preresolved_2106_ = lean_ctor_get(v_x_2093_, 3);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v_x_2093_, 0);
lean_dec(v_unused_2115_);
v___x_2108_ = v_x_2093_;
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_preresolved_2106_);
lean_inc(v_val_2105_);
lean_inc(v_rawVal_2104_);
lean_dec(v_x_2093_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v_info_2092_);
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_info_2092_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_rawVal_2104_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_val_2105_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_preresolved_2106_);
v___x_2111_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
}
case 1:
{
lean_object* v_info_2116_; lean_object* v_kind_2117_; lean_object* v_args_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2136_; 
v_info_2116_ = lean_ctor_get(v_x_2093_, 0);
v_kind_2117_ = lean_ctor_get(v_x_2093_, 1);
v_args_2118_ = lean_ctor_get(v_x_2093_, 2);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2120_ = v_x_2093_;
v_isShared_2121_ = v_isSharedCheck_2136_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_args_2118_);
lean_inc(v_kind_2117_);
lean_inc(v_info_2116_);
lean_dec(v_x_2093_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2136_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(v_info_2092_, v_args_2118_, v___x_2122_);
if (lean_obj_tag(v___x_2123_) == 1)
{
lean_object* v_val_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2134_; 
v_val_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2134_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_val_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2134_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 2, v_val_2124_);
v___x_2129_ = v___x_2120_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_info_2116_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_kind_2117_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_val_2124_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2129_);
v___x_2131_ = v___x_2126_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v___x_2135_; 
lean_dec(v___x_2123_);
lean_del_object(v___x_2120_);
lean_dec(v_kind_2117_);
lean_dec(v_info_2116_);
v___x_2135_ = lean_box(0);
return v___x_2135_;
}
}
}
default: 
{
lean_object* v___x_2137_; 
lean_dec(v_x_2093_);
lean_dec(v_info_2092_);
v___x_2137_ = lean_box(0);
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* v_info_2138_, lean_object* v_a_2139_, lean_object* v_i_2140_){
_start:
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = lean_array_get_size(v_a_2139_);
v___x_2142_ = lean_nat_dec_lt(v_i_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v_i_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_info_2138_);
v___x_2143_ = lean_box(0);
return v___x_2143_;
}
else
{
lean_object* v_v_2144_; lean_object* v___x_2145_; 
v_v_2144_ = lean_array_fget_borrowed(v_a_2139_, v_i_2140_);
lean_inc(v_v_2144_);
lean_inc(v_info_2138_);
v___x_2145_ = l_Lean_Syntax_setHeadInfoAux(v_info_2138_, v_v_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_add(v_i_2140_, v___x_2146_);
lean_dec(v_i_2140_);
v_i_2140_ = v___x_2147_;
goto _start;
}
else
{
lean_object* v_val_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v_info_2138_);
v_val_2149_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2151_ = v___x_2145_;
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_val_2149_);
lean_dec(v___x_2145_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = lean_array_fset(v_a_2139_, v_i_2140_, v_val_2149_);
lean_dec(v_i_2140_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2153_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* v_stx_2158_, lean_object* v_info_2159_){
_start:
{
lean_object* v___x_2160_; 
lean_inc(v_stx_2158_);
v___x_2160_ = l_Lean_Syntax_setHeadInfoAux(v_info_2159_, v_stx_2158_);
if (lean_obj_tag(v___x_2160_) == 0)
{
return v_stx_2158_;
}
else
{
lean_object* v_val_2161_; 
lean_dec(v_stx_2158_);
v_val_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_val_2161_);
lean_dec_ref_known(v___x_2160_, 1);
return v_val_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* v_info_2162_, lean_object* v_x_2163_){
_start:
{
switch(lean_obj_tag(v_x_2163_))
{
case 0:
{
lean_dec(v_info_2162_);
return v_x_2163_;
}
case 1:
{
lean_object* v_kind_2164_; lean_object* v_args_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v_kind_2164_ = lean_ctor_get(v_x_2163_, 1);
v_args_2165_ = lean_ctor_get(v_x_2163_, 2);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2163_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; 
v_unused_2173_ = lean_ctor_get(v_x_2163_, 0);
lean_dec(v_unused_2173_);
v___x_2167_ = v_x_2163_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_args_2165_);
lean_inc(v_kind_2164_);
lean_dec(v_x_2163_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v_info_2162_);
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_info_2162_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_kind_2164_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_args_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
case 2:
{
lean_object* v_val_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_val_2174_ = lean_ctor_get(v_x_2163_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_x_2163_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v_x_2163_, 0);
lean_dec(v_unused_2182_);
v___x_2176_ = v_x_2163_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_val_2174_);
lean_dec(v_x_2163_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v_info_2162_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_info_2162_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_val_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
default: 
{
lean_object* v_rawVal_2183_; lean_object* v_val_2184_; lean_object* v_preresolved_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_rawVal_2183_ = lean_ctor_get(v_x_2163_, 1);
v_val_2184_ = lean_ctor_get(v_x_2163_, 2);
v_preresolved_2185_ = lean_ctor_get(v_x_2163_, 3);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_x_2163_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v_x_2163_, 0);
lean_dec(v_unused_2193_);
v___x_2187_ = v_x_2163_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_preresolved_2185_);
lean_inc(v_val_2184_);
lean_inc(v_rawVal_2183_);
lean_dec(v_x_2163_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v_info_2162_);
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_info_2162_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_rawVal_2183_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_val_2184_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_preresolved_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* v_x_2197_){
_start:
{
switch(lean_obj_tag(v_x_2197_))
{
case 2:
{
lean_object* v_info_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; 
v_info_2198_ = lean_ctor_get(v_x_2197_, 0);
v___x_2199_ = 0;
v___x_2200_ = l_Lean_SourceInfo_getPos_x3f(v_info_2198_, v___x_2199_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v___x_2201_; 
lean_dec_ref_known(v_x_2197_, 2);
v___x_2201_ = lean_box(0);
return v___x_2201_;
}
else
{
lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v___x_2200_, 0);
lean_dec(v_unused_2209_);
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v_x_2197_);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_x_2197_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
case 3:
{
lean_object* v_info_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; 
v_info_2210_ = lean_ctor_get(v_x_2197_, 0);
v___x_2211_ = 0;
v___x_2212_ = l_Lean_SourceInfo_getPos_x3f(v_info_2210_, v___x_2211_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v___x_2213_; 
lean_dec_ref_known(v_x_2197_, 4);
v___x_2213_ = lean_box(0);
return v___x_2213_;
}
else
{
lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2212_, 0);
lean_dec(v_unused_2221_);
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v_x_2197_);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_x_2197_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
case 1:
{
lean_object* v_info_2222_; 
v_info_2222_ = lean_ctor_get(v_x_2197_, 0);
if (lean_obj_tag(v_info_2222_) == 2)
{
lean_object* v_args_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; size_t v_sz_2226_; size_t v___x_2227_; lean_object* v___x_2228_; lean_object* v_fst_2229_; 
v_args_2223_ = lean_ctor_get(v_x_2197_, 2);
lean_inc_ref(v_args_2223_);
lean_dec_ref_known(v_x_2197_, 3);
v___x_2224_ = lean_box(0);
v___x_2225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_2226_ = lean_array_size(v_args_2223_);
v___x_2227_ = ((size_t)0ULL);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_args_2223_, v_sz_2226_, v___x_2227_, v___x_2225_);
lean_dec_ref(v_args_2223_);
v_fst_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_fst_2229_);
lean_dec_ref(v___x_2228_);
if (lean_obj_tag(v_fst_2229_) == 0)
{
return v___x_2224_;
}
else
{
lean_object* v_val_2230_; 
v_val_2230_ = lean_ctor_get(v_fst_2229_, 0);
lean_inc(v_val_2230_);
lean_dec_ref_known(v_fst_2229_, 1);
return v_val_2230_;
}
}
else
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_x_2197_);
return v___x_2231_;
}
}
default: 
{
lean_object* v___x_2232_; 
lean_dec(v_x_2197_);
v___x_2232_ = lean_box(0);
return v___x_2232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* v_as_2233_, size_t v_sz_2234_, size_t v_i_2235_, lean_object* v_b_2236_){
_start:
{
uint8_t v___x_2237_; 
v___x_2237_ = lean_usize_dec_lt(v_i_2235_, v_sz_2234_);
if (v___x_2237_ == 0)
{
lean_inc_ref(v_b_2236_);
return v_b_2236_;
}
else
{
lean_object* v___x_2238_; lean_object* v_a_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_box(0);
v_a_2239_ = lean_array_uget_borrowed(v_as_2233_, v_i_2235_);
lean_inc(v_a_2239_);
v___x_2240_ = l_Lean_Syntax_getHead_x3f(v_a_2239_);
if (lean_obj_tag(v___x_2240_) == 1)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2238_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; size_t v___x_2244_; size_t v___x_2245_; 
lean_dec(v___x_2240_);
v___x_2243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_2244_ = ((size_t)1ULL);
v___x_2245_ = lean_usize_add(v_i_2235_, v___x_2244_);
v_i_2235_ = v___x_2245_;
v_b_2236_ = v___x_2243_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* v_as_2247_, lean_object* v_sz_2248_, lean_object* v_i_2249_, lean_object* v_b_2250_){
_start:
{
size_t v_sz_boxed_2251_; size_t v_i_boxed_2252_; lean_object* v_res_2253_; 
v_sz_boxed_2251_ = lean_unbox_usize(v_sz_2248_);
lean_dec(v_sz_2248_);
v_i_boxed_2252_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(v_as_2247_, v_sz_boxed_2251_, v_i_boxed_2252_, v_b_2250_);
lean_dec_ref(v_b_2250_);
lean_dec_ref(v_as_2247_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* v_target_2254_, lean_object* v_source_2255_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2256_ = l_Lean_Syntax_getHeadInfo(v_source_2255_);
v___x_2257_ = l_Lean_Syntax_setHeadInfo(v_target_2254_, v___x_2256_);
v___x_2258_ = l_Lean_Syntax_getTailInfo(v_source_2255_);
v___x_2259_ = l_Lean_Syntax_setTailInfo(v___x_2257_, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* v_target_2260_, lean_object* v_source_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_target_2260_, v_source_2261_);
lean_dec(v_source_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* v_stx_2263_){
_start:
{
uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = 0;
v___x_2265_ = l_Lean_SourceInfo_fromRef(v_stx_2263_, v___x_2264_);
v___x_2266_ = l_Lean_Syntax_setHeadInfo(v_stx_2263_, v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* v_val_2267_, lean_object* v_withRef_2268_, lean_object* v_x_2269_, lean_object* v_oldRef_2270_){
_start:
{
lean_object* v_ref_2271_; lean_object* v___x_2272_; 
v_ref_2271_ = l_Lean_replaceRef(v_val_2267_, v_oldRef_2270_);
v___x_2272_ = lean_apply_3(v_withRef_2268_, lean_box(0), v_ref_2271_, v_x_2269_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* v_val_2273_, lean_object* v_withRef_2274_, lean_object* v_x_2275_, lean_object* v_oldRef_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_withHeadRefOnly___redArg___lam__0(v_val_2273_, v_withRef_2274_, v_x_2275_, v_oldRef_2276_);
lean_dec(v_oldRef_2276_);
lean_dec(v_val_2273_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* v_x_2278_, lean_object* v_withRef_2279_, lean_object* v_toBind_2280_, lean_object* v_getRef_2281_, lean_object* v_____do__lift_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Syntax_getHead_x3f(v_____do__lift_2282_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_dec(v_getRef_2281_);
lean_dec(v_toBind_2280_);
lean_dec(v_withRef_2279_);
return v_x_2278_;
}
else
{
lean_object* v_val_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; 
v_val_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_val_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___f_2285_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2285_, 0, v_val_2284_);
lean_closure_set(v___f_2285_, 1, v_withRef_2279_);
lean_closure_set(v___f_2285_, 2, v_x_2278_);
v___x_2286_ = lean_apply_4(v_toBind_2280_, lean_box(0), lean_box(0), v_getRef_2281_, v___f_2285_);
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_x_2289_){
_start:
{
lean_object* v_toBind_2290_; lean_object* v_getRef_2291_; lean_object* v_withRef_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; 
v_toBind_2290_ = lean_ctor_get(v_inst_2287_, 1);
lean_inc_n(v_toBind_2290_, 2);
lean_dec_ref(v_inst_2287_);
v_getRef_2291_ = lean_ctor_get(v_inst_2288_, 0);
lean_inc_n(v_getRef_2291_, 2);
v_withRef_2292_ = lean_ctor_get(v_inst_2288_, 1);
lean_inc(v_withRef_2292_);
lean_dec_ref(v_inst_2288_);
v___f_2293_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2293_, 0, v_x_2289_);
lean_closure_set(v___f_2293_, 1, v_withRef_2292_);
lean_closure_set(v___f_2293_, 2, v_toBind_2290_);
lean_closure_set(v___f_2293_, 3, v_getRef_2291_);
v___x_2294_ = lean_apply_4(v_toBind_2290_, lean_box(0), lean_box(0), v_getRef_2291_, v___f_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* v_m_2295_, lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_00_u03b1_2298_, lean_object* v_x_2299_){
_start:
{
lean_object* v_toBind_2300_; lean_object* v_getRef_2301_; lean_object* v_withRef_2302_; lean_object* v___f_2303_; lean_object* v___x_2304_; 
v_toBind_2300_ = lean_ctor_get(v_inst_2296_, 1);
lean_inc_n(v_toBind_2300_, 2);
lean_dec_ref(v_inst_2296_);
v_getRef_2301_ = lean_ctor_get(v_inst_2297_, 0);
lean_inc_n(v_getRef_2301_, 2);
v_withRef_2302_ = lean_ctor_get(v_inst_2297_, 1);
lean_inc(v_withRef_2302_);
lean_dec_ref(v_inst_2297_);
v___f_2303_ = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2303_, 0, v_x_2299_);
lean_closure_set(v___f_2303_, 1, v_withRef_2302_);
lean_closure_set(v___f_2303_, 2, v_toBind_2300_);
lean_closure_set(v___f_2303_, 3, v_getRef_2301_);
v___x_2304_ = lean_apply_4(v_toBind_2300_, lean_box(0), lean_box(0), v_getRef_2301_, v___f_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t v___x_2314_, lean_object* v_k_2315_){
_start:
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_2317_ = lean_name_eq(v_k_2315_, v___x_2316_);
if (v___x_2317_ == 0)
{
return v___x_2314_;
}
else
{
uint8_t v___x_2318_; 
v___x_2318_ = 0;
return v___x_2318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* v___x_2319_, lean_object* v_k_2320_){
_start:
{
uint8_t v___x_1783__boxed_2321_; uint8_t v_res_2322_; lean_object* v_r_2323_; 
v___x_1783__boxed_2321_ = lean_unbox(v___x_2319_);
v_res_2322_ = l_Lean_expandMacros___lam__0(v___x_1783__boxed_2321_, v_k_2320_);
lean_dec(v_k_2320_);
v_r_2323_ = lean_box(v_res_2322_);
return v_r_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* v_stx_2325_, lean_object* v_p_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
if (lean_obj_tag(v_stx_2325_) == 1)
{
lean_object* v_info_2329_; lean_object* v_kind_2330_; lean_object* v_args_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v_info_2329_ = lean_ctor_get(v_stx_2325_, 0);
v_kind_2330_ = lean_ctor_get(v_stx_2325_, 1);
v_args_2331_ = lean_ctor_get(v_stx_2325_, 2);
lean_inc(v_kind_2330_);
v___x_2332_ = lean_apply_1(v_p_2326_, v_kind_2330_);
v___x_2333_ = lean_unbox(v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; 
lean_dec_ref(v_a_2327_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_stx_2325_);
lean_ctor_set(v___x_2334_, 1, v_a_2328_);
return v___x_2334_;
}
else
{
lean_object* v_methods_2335_; lean_object* v_quotContext_2336_; lean_object* v_currMacroScope_2337_; lean_object* v_currRecDepth_2338_; lean_object* v_maxRecDepth_2339_; lean_object* v_ref_2340_; lean_object* v_ref_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_methods_2335_ = lean_ctor_get(v_a_2327_, 0);
lean_inc_n(v_methods_2335_, 2);
v_quotContext_2336_ = lean_ctor_get(v_a_2327_, 1);
lean_inc_n(v_quotContext_2336_, 2);
v_currMacroScope_2337_ = lean_ctor_get(v_a_2327_, 2);
lean_inc_n(v_currMacroScope_2337_, 2);
v_currRecDepth_2338_ = lean_ctor_get(v_a_2327_, 3);
lean_inc_n(v_currRecDepth_2338_, 2);
v_maxRecDepth_2339_ = lean_ctor_get(v_a_2327_, 4);
lean_inc_n(v_maxRecDepth_2339_, 2);
v_ref_2340_ = lean_ctor_get(v_a_2327_, 5);
lean_inc(v_ref_2340_);
lean_dec_ref(v_a_2327_);
v_ref_2341_ = l_Lean_replaceRef(v_stx_2325_, v_ref_2340_);
lean_dec(v_ref_2340_);
lean_inc(v_ref_2341_);
v___x_2342_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2342_, 0, v_methods_2335_);
lean_ctor_set(v___x_2342_, 1, v_quotContext_2336_);
lean_ctor_set(v___x_2342_, 2, v_currMacroScope_2337_);
lean_ctor_set(v___x_2342_, 3, v_currRecDepth_2338_);
lean_ctor_set(v___x_2342_, 4, v_maxRecDepth_2339_);
lean_ctor_set(v___x_2342_, 5, v_ref_2341_);
lean_inc_ref(v_stx_2325_);
v___x_2343_ = l_Lean_Macro_expandMacro_x3f(v_stx_2325_, v___x_2342_, v_a_2328_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
if (lean_obj_tag(v_a_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref_known(v___x_2342_, 6);
v_a_2345_ = lean_ctor_get(v___x_2343_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v___x_2343_, 0);
lean_dec(v_unused_2391_);
v___x_2347_ = v___x_2343_;
v_isShared_2348_ = v_isSharedCheck_2390_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2343_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2390_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_nat_dec_eq(v_currRecDepth_2338_, v_maxRecDepth_2339_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2381_; 
lean_inc_ref(v_args_2331_);
lean_inc(v_kind_2330_);
lean_inc(v_info_2329_);
lean_del_object(v___x_2347_);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_stx_2325_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; lean_object* v_unused_2383_; lean_object* v_unused_2384_; 
v_unused_2382_ = lean_ctor_get(v_stx_2325_, 2);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_stx_2325_, 1);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_stx_2325_, 0);
lean_dec(v_unused_2384_);
v___x_2351_ = v_stx_2325_;
v_isShared_2352_ = v_isSharedCheck_2381_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v_stx_2325_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2381_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; size_t v_sz_2356_; size_t v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_nat_add(v_currRecDepth_2338_, v___x_2353_);
lean_dec(v_currRecDepth_2338_);
v___x_2355_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2355_, 0, v_methods_2335_);
lean_ctor_set(v___x_2355_, 1, v_quotContext_2336_);
lean_ctor_set(v___x_2355_, 2, v_currMacroScope_2337_);
lean_ctor_set(v___x_2355_, 3, v___x_2354_);
lean_ctor_set(v___x_2355_, 4, v_maxRecDepth_2339_);
lean_ctor_set(v___x_2355_, 5, v_ref_2341_);
v_sz_2356_ = lean_array_size(v_args_2331_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = lean_unbox(v___x_2332_);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_2358_, v_sz_2356_, v___x_2357_, v_args_2331_, v___x_2355_, v_a_2345_);
lean_dec_ref_known(v___x_2355_, 6);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2371_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_a_2361_ = lean_ctor_get(v___x_2359_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2363_ = v___x_2359_;
v_isShared_2364_ = v_isSharedCheck_2371_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2371_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 2, v_a_2360_);
v___x_2366_ = v___x_2351_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_info_2329_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_kind_2330_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_a_2360_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2366_);
v___x_2368_ = v___x_2363_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_a_2361_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_del_object(v___x_2351_);
lean_dec(v_kind_2330_);
lean_dec(v_info_2329_);
v_a_2372_ = lean_ctor_get(v___x_2359_, 0);
v_a_2373_ = lean_ctor_get(v___x_2359_, 1);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2359_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_inc(v_a_2372_);
lean_dec(v___x_2359_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2372_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_dec(v_ref_2341_);
lean_dec(v_maxRecDepth_2339_);
lean_dec(v_currRecDepth_2338_);
lean_dec(v_currMacroScope_2337_);
lean_dec(v_quotContext_2336_);
lean_dec(v_methods_2335_);
v___x_2385_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_stx_2325_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2386_);
v___x_2388_ = v___x_2347_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_a_2345_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v_val_2393_; lean_object* v___f_2394_; 
lean_dec(v_ref_2341_);
lean_dec(v_maxRecDepth_2339_);
lean_dec(v_currRecDepth_2338_);
lean_dec(v_currMacroScope_2337_);
lean_dec(v_quotContext_2336_);
lean_dec(v_methods_2335_);
lean_dec_ref_known(v_stx_2325_, 3);
v_a_2392_ = lean_ctor_get(v___x_2343_, 1);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2343_, 2);
v_val_2393_ = lean_ctor_get(v_a_2344_, 0);
lean_inc(v_val_2393_);
lean_dec_ref_known(v_a_2344_, 1);
v___f_2394_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2394_, 0, v___x_2332_);
v_stx_2325_ = v_val_2393_;
v_p_2326_ = v___f_2394_;
v_a_2327_ = v___x_2342_;
v_a_2328_ = v_a_2392_;
goto _start;
}
}
else
{
lean_object* v_a_2396_; lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref_known(v___x_2342_, 6);
lean_dec(v_ref_2341_);
lean_dec(v_maxRecDepth_2339_);
lean_dec(v_currRecDepth_2338_);
lean_dec(v_currMacroScope_2337_);
lean_dec(v_quotContext_2336_);
lean_dec(v_methods_2335_);
lean_dec_ref_known(v_stx_2325_, 3);
v_a_2396_ = lean_ctor_get(v___x_2343_, 0);
v_a_2397_ = lean_ctor_get(v___x_2343_, 1);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2343_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_inc(v_a_2396_);
lean_dec(v___x_2343_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2396_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
else
{
lean_object* v___x_2405_; 
lean_dec_ref(v_a_2327_);
lean_dec_ref(v_p_2326_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_stx_2325_);
lean_ctor_set(v___x_2405_, 1, v_a_2328_);
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t v___x_2406_, size_t v_sz_2407_, size_t v_i_2408_, lean_object* v_bs_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
uint8_t v___x_2412_; 
v___x_2412_ = lean_usize_dec_lt(v_i_2408_, v_sz_2407_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v_bs_2409_);
lean_ctor_set(v___x_2413_, 1, v___y_2411_);
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v_v_2416_; lean_object* v___x_2417_; 
v___x_2414_ = lean_box(v___x_2406_);
v___f_2415_ = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2415_, 0, v___x_2414_);
v_v_2416_ = lean_array_uget_borrowed(v_bs_2409_, v_i_2408_);
lean_inc_ref(v___y_2410_);
lean_inc(v_v_2416_);
v___x_2417_ = l_Lean_expandMacros(v_v_2416_, v___f_2415_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v_a_2419_; lean_object* v___x_2420_; lean_object* v_bs_x27_2421_; size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
v_a_2419_ = lean_ctor_get(v___x_2417_, 1);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2417_, 2);
v___x_2420_ = lean_unsigned_to_nat(0u);
v_bs_x27_2421_ = lean_array_uset(v_bs_2409_, v_i_2408_, v___x_2420_);
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2408_, v___x_2422_);
v___x_2424_ = lean_array_uset(v_bs_x27_2421_, v_i_2408_, v_a_2418_);
v_i_2408_ = v___x_2423_;
v_bs_2409_ = v___x_2424_;
v___y_2411_ = v_a_2419_;
goto _start;
}
else
{
lean_object* v_a_2426_; lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec_ref(v_bs_2409_);
v_a_2426_ = lean_ctor_get(v___x_2417_, 0);
v_a_2427_ = lean_ctor_get(v___x_2417_, 1);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2417_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_inc(v_a_2426_);
lean_dec(v___x_2417_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2426_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* v___x_2435_, lean_object* v_sz_2436_, lean_object* v_i_2437_, lean_object* v_bs_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v___x_1802__boxed_2441_; size_t v_sz_boxed_2442_; size_t v_i_boxed_2443_; lean_object* v_res_2444_; 
v___x_1802__boxed_2441_ = lean_unbox(v___x_2435_);
v_sz_boxed_2442_ = lean_unbox_usize(v_sz_2436_);
lean_dec(v_sz_2436_);
v_i_boxed_2443_ = lean_unbox_usize(v_i_2437_);
lean_dec(v_i_2437_);
v_res_2444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(v___x_1802__boxed_2441_, v_sz_boxed_2442_, v_i_boxed_2443_, v_bs_2438_, v___y_2439_, v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* v_src_2445_, lean_object* v_val_2446_, uint8_t v_canonical_2447_){
_start:
{
lean_object* v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2448_ = l_Lean_SourceInfo_fromRef(v_src_2445_, v_canonical_2447_);
v___x_2449_ = 1;
lean_inc(v_val_2446_);
v___x_2450_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2446_, v___x_2449_);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = lean_string_utf8_byte_size(v___x_2450_);
v___x_2453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2450_);
lean_ctor_set(v___x_2453_, 1, v___x_2451_);
lean_ctor_set(v___x_2453_, 2, v___x_2452_);
v___x_2454_ = lean_box(0);
v___x_2455_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2448_);
lean_ctor_set(v___x_2455_, 1, v___x_2453_);
lean_ctor_set(v___x_2455_, 2, v_val_2446_);
lean_ctor_set(v___x_2455_, 3, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* v_src_2456_, lean_object* v_val_2457_, lean_object* v_canonical_2458_){
_start:
{
uint8_t v_canonical_boxed_2459_; lean_object* v_res_2460_; 
v_canonical_boxed_2459_ = lean_unbox(v_canonical_2458_);
v_res_2460_ = l_Lean_mkIdentFrom(v_src_2456_, v_val_2457_, v_canonical_boxed_2459_);
lean_dec(v_src_2456_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* v_val_2461_, uint8_t v_canonical_2462_, lean_object* v_toPure_2463_, lean_object* v_____do__lift_2464_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = l_Lean_mkIdentFrom(v_____do__lift_2464_, v_val_2461_, v_canonical_2462_);
v___x_2466_ = lean_apply_2(v_toPure_2463_, lean_box(0), v___x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* v_val_2467_, lean_object* v_canonical_2468_, lean_object* v_toPure_2469_, lean_object* v_____do__lift_2470_){
_start:
{
uint8_t v_canonical_boxed_2471_; lean_object* v_res_2472_; 
v_canonical_boxed_2471_ = lean_unbox(v_canonical_2468_);
v_res_2472_ = l_Lean_mkIdentFromRef___redArg___lam__0(v_val_2467_, v_canonical_boxed_2471_, v_toPure_2469_, v_____do__lift_2470_);
lean_dec(v_____do__lift_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_val_2475_, uint8_t v_canonical_2476_){
_start:
{
lean_object* v_toApplicative_2477_; lean_object* v_toBind_2478_; lean_object* v_getRef_2479_; lean_object* v_toPure_2480_; lean_object* v___x_2481_; lean_object* v___f_2482_; lean_object* v___x_2483_; 
v_toApplicative_2477_ = lean_ctor_get(v_inst_2473_, 0);
lean_inc_ref(v_toApplicative_2477_);
v_toBind_2478_ = lean_ctor_get(v_inst_2473_, 1);
lean_inc(v_toBind_2478_);
lean_dec_ref(v_inst_2473_);
v_getRef_2479_ = lean_ctor_get(v_inst_2474_, 0);
lean_inc(v_getRef_2479_);
lean_dec_ref(v_inst_2474_);
v_toPure_2480_ = lean_ctor_get(v_toApplicative_2477_, 1);
lean_inc(v_toPure_2480_);
lean_dec_ref(v_toApplicative_2477_);
v___x_2481_ = lean_box(v_canonical_2476_);
v___f_2482_ = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2482_, 0, v_val_2475_);
lean_closure_set(v___f_2482_, 1, v___x_2481_);
lean_closure_set(v___f_2482_, 2, v_toPure_2480_);
v___x_2483_ = lean_apply_4(v_toBind_2478_, lean_box(0), lean_box(0), v_getRef_2479_, v___f_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_val_2486_, lean_object* v_canonical_2487_){
_start:
{
uint8_t v_canonical_boxed_2488_; lean_object* v_res_2489_; 
v_canonical_boxed_2488_ = lean_unbox(v_canonical_2487_);
v_res_2489_ = l_Lean_mkIdentFromRef___redArg(v_inst_2484_, v_inst_2485_, v_val_2486_, v_canonical_boxed_2488_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* v_m_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_val_2493_, uint8_t v_canonical_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_mkIdentFromRef___redArg(v_inst_2491_, v_inst_2492_, v_val_2493_, v_canonical_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* v_m_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_val_2499_, lean_object* v_canonical_2500_){
_start:
{
uint8_t v_canonical_boxed_2501_; lean_object* v_res_2502_; 
v_canonical_boxed_2501_ = lean_unbox(v_canonical_2500_);
v_res_2502_ = l_Lean_mkIdentFromRef(v_m_2496_, v_inst_2497_, v_inst_2498_, v_val_2499_, v_canonical_boxed_2501_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* v_src_2506_, lean_object* v_c_2507_, uint8_t v_canonical_2508_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v_id_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2509_ = ((lean_object*)(l_Lean_mkCIdentFrom___closed__1));
v___x_2510_ = lean_unsigned_to_nat(0u);
lean_inc(v_c_2507_);
v_id_2511_ = l_Lean_addMacroScope(v___x_2509_, v_c_2507_, v___x_2510_);
v___x_2512_ = l_Lean_SourceInfo_fromRef(v_src_2506_, v_canonical_2508_);
v___x_2513_ = 1;
lean_inc(v_id_2511_);
v___x_2514_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_id_2511_, v___x_2513_);
v___x_2515_ = lean_string_utf8_byte_size(v___x_2514_);
v___x_2516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2510_);
lean_ctor_set(v___x_2516_, 2, v___x_2515_);
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2518_, 0, v_c_2507_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___x_2517_);
v___x_2520_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2512_);
lean_ctor_set(v___x_2520_, 1, v___x_2516_);
lean_ctor_set(v___x_2520_, 2, v_id_2511_);
lean_ctor_set(v___x_2520_, 3, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* v_src_2521_, lean_object* v_c_2522_, lean_object* v_canonical_2523_){
_start:
{
uint8_t v_canonical_boxed_2524_; lean_object* v_res_2525_; 
v_canonical_boxed_2524_ = lean_unbox(v_canonical_2523_);
v_res_2525_ = l_Lean_mkCIdentFrom(v_src_2521_, v_c_2522_, v_canonical_boxed_2524_);
lean_dec(v_src_2521_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* v_c_2526_, uint8_t v_canonical_2527_, lean_object* v_toPure_2528_, lean_object* v_____do__lift_2529_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = l_Lean_mkCIdentFrom(v_____do__lift_2529_, v_c_2526_, v_canonical_2527_);
v___x_2531_ = lean_apply_2(v_toPure_2528_, lean_box(0), v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* v_c_2532_, lean_object* v_canonical_2533_, lean_object* v_toPure_2534_, lean_object* v_____do__lift_2535_){
_start:
{
uint8_t v_canonical_boxed_2536_; lean_object* v_res_2537_; 
v_canonical_boxed_2536_ = lean_unbox(v_canonical_2533_);
v_res_2537_ = l_Lean_mkCIdentFromRef___redArg___lam__0(v_c_2532_, v_canonical_boxed_2536_, v_toPure_2534_, v_____do__lift_2535_);
lean_dec(v_____do__lift_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_c_2540_, uint8_t v_canonical_2541_){
_start:
{
lean_object* v_toApplicative_2542_; lean_object* v_toBind_2543_; lean_object* v_getRef_2544_; lean_object* v_toPure_2545_; lean_object* v___x_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; 
v_toApplicative_2542_ = lean_ctor_get(v_inst_2538_, 0);
lean_inc_ref(v_toApplicative_2542_);
v_toBind_2543_ = lean_ctor_get(v_inst_2538_, 1);
lean_inc(v_toBind_2543_);
lean_dec_ref(v_inst_2538_);
v_getRef_2544_ = lean_ctor_get(v_inst_2539_, 0);
lean_inc(v_getRef_2544_);
lean_dec_ref(v_inst_2539_);
v_toPure_2545_ = lean_ctor_get(v_toApplicative_2542_, 1);
lean_inc(v_toPure_2545_);
lean_dec_ref(v_toApplicative_2542_);
v___x_2546_ = lean_box(v_canonical_2541_);
v___f_2547_ = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2547_, 0, v_c_2540_);
lean_closure_set(v___f_2547_, 1, v___x_2546_);
lean_closure_set(v___f_2547_, 2, v_toPure_2545_);
v___x_2548_ = lean_apply_4(v_toBind_2543_, lean_box(0), lean_box(0), v_getRef_2544_, v___f_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_c_2551_, lean_object* v_canonical_2552_){
_start:
{
uint8_t v_canonical_boxed_2553_; lean_object* v_res_2554_; 
v_canonical_boxed_2553_ = lean_unbox(v_canonical_2552_);
v_res_2554_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2549_, v_inst_2550_, v_c_2551_, v_canonical_boxed_2553_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* v_m_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_c_2558_, uint8_t v_canonical_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_mkCIdentFromRef___redArg(v_inst_2556_, v_inst_2557_, v_c_2558_, v_canonical_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* v_m_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_c_2564_, lean_object* v_canonical_2565_){
_start:
{
uint8_t v_canonical_boxed_2566_; lean_object* v_res_2567_; 
v_canonical_boxed_2566_ = lean_unbox(v_canonical_2565_);
v_res_2567_ = l_Lean_mkCIdentFromRef(v_m_2561_, v_inst_2562_, v_inst_2563_, v_c_2564_, v_canonical_boxed_2566_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* v_c_2568_){
_start:
{
lean_object* v___x_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_box(0);
v___x_2570_ = 0;
v___x_2571_ = l_Lean_mkCIdentFrom(v___x_2569_, v_c_2568_, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdent(lean_object* v_val_2572_){
_start:
{
lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2573_ = lean_box(2);
v___x_2574_ = 1;
lean_inc(v_val_2572_);
v___x_2575_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_2572_, v___x_2574_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_string_utf8_byte_size(v___x_2575_);
v___x_2578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2575_);
lean_ctor_set(v___x_2578_, 1, v___x_2576_);
lean_ctor_set(v___x_2578_, 2, v___x_2577_);
v___x_2579_ = lean_box(0);
v___x_2580_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2573_);
lean_ctor_set(v___x_2580_, 1, v___x_2578_);
lean_ctor_set(v___x_2580_, 2, v_val_2572_);
lean_ctor_set(v___x_2580_, 3, v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* v_args_2584_){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = ((lean_object*)(l_Lean_mkGroupNode___closed__1));
v___x_2586_ = lean_box(2);
v___x_2587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
lean_ctor_set(v___x_2587_, 1, v___x_2585_);
lean_ctor_set(v___x_2587_, 2, v_args_2584_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* v_sep_2588_, lean_object* v_as_2589_, size_t v_sz_2590_, size_t v_i_2591_, lean_object* v_b_2592_){
_start:
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_usize_dec_lt(v_i_2591_, v_sz_2590_);
if (v___x_2593_ == 0)
{
lean_dec(v_sep_2588_);
return v_b_2592_;
}
else
{
lean_object* v_fst_2594_; lean_object* v_snd_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2615_; 
v_fst_2594_ = lean_ctor_get(v_b_2592_, 0);
v_snd_2595_ = lean_ctor_get(v_b_2592_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_b_2592_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2597_ = v_b_2592_;
v_isShared_2598_ = v_isSharedCheck_2615_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_snd_2595_);
lean_inc(v_fst_2594_);
lean_dec(v_b_2592_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2615_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v_r_2600_; lean_object* v_i_2609_; lean_object* v_a_2610_; uint8_t v___x_2611_; 
v_i_2609_ = lean_unsigned_to_nat(0u);
v_a_2610_ = lean_array_uget_borrowed(v_as_2589_, v_i_2591_);
v___x_2611_ = lean_nat_dec_lt(v_i_2609_, v_fst_2594_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; 
lean_inc(v_a_2610_);
v___x_2612_ = lean_array_push(v_snd_2595_, v_a_2610_);
v_r_2600_ = v___x_2612_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_inc(v_sep_2588_);
v___x_2613_ = lean_array_push(v_snd_2595_, v_sep_2588_);
lean_inc(v_a_2610_);
v___x_2614_ = lean_array_push(v___x_2613_, v_a_2610_);
v_r_2600_ = v___x_2614_;
goto v___jp_2599_;
}
v___jp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2601_ = lean_unsigned_to_nat(1u);
v___x_2602_ = lean_nat_add(v_fst_2594_, v___x_2601_);
lean_dec(v_fst_2594_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 1, v_r_2600_);
lean_ctor_set(v___x_2597_, 0, v___x_2602_);
v___x_2604_ = v___x_2597_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_r_2600_);
v___x_2604_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
size_t v___x_2605_; size_t v___x_2606_; 
v___x_2605_ = ((size_t)1ULL);
v___x_2606_ = lean_usize_add(v_i_2591_, v___x_2605_);
v_i_2591_ = v___x_2606_;
v_b_2592_ = v___x_2604_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* v_sep_2616_, lean_object* v_as_2617_, lean_object* v_sz_2618_, lean_object* v_i_2619_, lean_object* v_b_2620_){
_start:
{
size_t v_sz_boxed_2621_; size_t v_i_boxed_2622_; lean_object* v_res_2623_; 
v_sz_boxed_2621_ = lean_unbox_usize(v_sz_2618_);
lean_dec(v_sz_2618_);
v_i_boxed_2622_ = lean_unbox_usize(v_i_2619_);
lean_dec(v_i_2619_);
v_res_2623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2616_, v_as_2617_, v_sz_boxed_2621_, v_i_boxed_2622_, v_b_2620_);
lean_dec_ref(v_as_2617_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* v_as_2629_, lean_object* v_sep_2630_){
_start:
{
lean_object* v___x_2631_; size_t v_sz_2632_; size_t v___x_2633_; lean_object* v___x_2634_; lean_object* v_snd_2635_; 
v___x_2631_ = ((lean_object*)(l_Lean_mkSepArray___closed__1));
v_sz_2632_ = lean_array_size(v_as_2629_);
v___x_2633_ = ((size_t)0ULL);
v___x_2634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(v_sep_2630_, v_as_2629_, v_sz_2632_, v___x_2633_, v___x_2631_);
v_snd_2635_ = lean_ctor_get(v___x_2634_, 1);
lean_inc(v_snd_2635_);
lean_dec_ref(v___x_2634_);
return v_snd_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* v_as_2636_, lean_object* v_sep_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_mkSepArray(v_as_2636_, v_sep_2637_);
lean_dec_ref(v_as_2636_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* v_arg_2646_){
_start:
{
if (lean_obj_tag(v_arg_2646_) == 0)
{
lean_object* v___x_2647_; 
v___x_2647_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
return v___x_2647_;
}
else
{
lean_object* v_val_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v_val_2648_ = lean_ctor_get(v_arg_2646_, 0);
lean_inc(v_val_2648_);
lean_dec_ref_known(v_arg_2646_, 1);
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_mk_empty_array_with_capacity(v___x_2649_);
v___x_2651_ = lean_array_push(v___x_2650_, v_val_2648_);
v___x_2652_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2653_ = lean_box(2);
v___x_2654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v___x_2652_);
lean_ctor_set(v___x_2654_, 2, v___x_2651_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* v_ref_2661_, uint8_t v_canonical_2662_){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2663_ = ((lean_object*)(l_Lean_mkHole___closed__1));
v___x_2664_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0));
v___x_2665_ = l_Lean_mkAtomFrom(v_ref_2661_, v___x_2664_, v_canonical_2662_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_mk_empty_array_with_capacity(v___x_2666_);
v___x_2668_ = lean_array_push(v___x_2667_, v___x_2665_);
v___x_2669_ = lean_box(2);
v___x_2670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___x_2663_);
lean_ctor_set(v___x_2670_, 2, v___x_2668_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* v_ref_2671_, lean_object* v_canonical_2672_){
_start:
{
uint8_t v_canonical_boxed_2673_; lean_object* v_res_2674_; 
v_canonical_boxed_2673_ = lean_unbox(v_canonical_2672_);
v_res_2674_ = l_Lean_mkHole(v_ref_2671_, v_canonical_boxed_2673_);
lean_dec(v_ref_2671_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* v_a_2675_, lean_object* v_sep_2676_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2677_ = l_Lean_mkSepArray(v_a_2675_, v_sep_2676_);
v___x_2678_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2679_ = lean_box(2);
v___x_2680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
lean_ctor_set(v___x_2680_, 1, v___x_2678_);
lean_ctor_set(v___x_2680_, 2, v___x_2677_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* v_a_2681_, lean_object* v_sep_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_Syntax_mkSep(v_a_2681_, v_sep_2682_);
lean_dec_ref(v_a_2681_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* v_sep_2690_, lean_object* v_elems_2691_){
_start:
{
uint8_t v___x_2692_; 
lean_inc_ref(v_sep_2690_);
v___x_2692_ = lean_string_isempty(v_sep_2690_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = l_Lean_mkAtom(v_sep_2690_);
v___x_2694_ = l_Lean_mkSepArray(v_elems_2691_, v___x_2693_);
return v___x_2694_;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec_ref(v_sep_2690_);
v___x_2695_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___x_2696_ = l_Lean_mkSepArray(v_elems_2691_, v___x_2695_);
return v___x_2696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* v_sep_2697_, lean_object* v_elems_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2697_, v_elems_2698_);
lean_dec_ref(v_elems_2698_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* v_elems_2700_, lean_object* v_toPure_2701_, lean_object* v_sep_2702_, lean_object* v_ref_2703_){
_start:
{
lean_object* v___y_2705_; uint8_t v___x_2708_; 
lean_inc_ref(v_sep_2702_);
v___x_2708_ = lean_string_isempty(v_sep_2702_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_mkAtomFrom(v_ref_2703_, v_sep_2702_, v___x_2708_);
v___y_2705_ = v___x_2709_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2710_; 
lean_dec_ref(v_sep_2702_);
v___x_2710_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__1));
v___y_2705_ = v___x_2710_;
goto v___jp_2704_;
}
v___jp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = l_Lean_mkSepArray(v_elems_2700_, v___y_2705_);
v___x_2707_ = lean_apply_2(v_toPure_2701_, lean_box(0), v___x_2706_);
return v___x_2707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* v_elems_2711_, lean_object* v_toPure_2712_, lean_object* v_sep_2713_, lean_object* v_ref_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(v_elems_2711_, v_toPure_2712_, v_sep_2713_, v_ref_2714_);
lean_dec(v_ref_2714_);
lean_dec_ref(v_elems_2711_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_sep_2718_, lean_object* v_elems_2719_){
_start:
{
lean_object* v_toApplicative_2720_; lean_object* v_toBind_2721_; lean_object* v_getRef_2722_; lean_object* v_toPure_2723_; lean_object* v___f_2724_; lean_object* v___x_2725_; 
v_toApplicative_2720_ = lean_ctor_get(v_inst_2716_, 0);
lean_inc_ref(v_toApplicative_2720_);
v_toBind_2721_ = lean_ctor_get(v_inst_2716_, 1);
lean_inc(v_toBind_2721_);
lean_dec_ref(v_inst_2716_);
v_getRef_2722_ = lean_ctor_get(v_inst_2717_, 0);
lean_inc(v_getRef_2722_);
lean_dec_ref(v_inst_2717_);
v_toPure_2723_ = lean_ctor_get(v_toApplicative_2720_, 1);
lean_inc(v_toPure_2723_);
lean_dec_ref(v_toApplicative_2720_);
v___f_2724_ = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2724_, 0, v_elems_2719_);
lean_closure_set(v___f_2724_, 1, v_toPure_2723_);
lean_closure_set(v___f_2724_, 2, v_sep_2718_);
v___x_2725_ = lean_apply_4(v_toBind_2721_, lean_box(0), lean_box(0), v_getRef_2722_, v___f_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* v_m_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_sep_2729_, lean_object* v_elems_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(v_inst_2727_, v_inst_2728_, v_sep_2729_, v_elems_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* v_sep_2732_, lean_object* v_elems_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2732_, v_elems_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* v_sep_2735_, lean_object* v_elems_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Syntax_TSepArray_ofElems___redArg(v_sep_2735_, v_elems_2736_);
lean_dec_ref(v_elems_2736_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* v_k_2738_, lean_object* v_sep_2739_, lean_object* v_elems_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Syntax_SepArray_ofElems(v_sep_2739_, v_elems_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* v_k_2742_, lean_object* v_sep_2743_, lean_object* v_elems_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Syntax_TSepArray_ofElems(v_k_2742_, v_sep_2743_, v_elems_2744_);
lean_dec_ref(v_elems_2744_);
lean_dec(v_k_2742_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* v_k_2746_, lean_object* v_sep_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(v___x_2748_, 0, v_k_2746_);
lean_closure_set(v___x_2748_, 1, v_sep_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* v_fn_2755_, lean_object* v_x_2756_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2757_ = lean_array_get_size(v_x_2756_);
v___x_2758_ = lean_unsigned_to_nat(0u);
v___x_2759_ = lean_nat_dec_eq(v___x_2757_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2760_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_2761_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_2762_ = lean_box(2);
v___x_2763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
lean_ctor_set(v___x_2763_, 1, v___x_2761_);
lean_ctor_set(v___x_2763_, 2, v_x_2756_);
v___x_2764_ = lean_unsigned_to_nat(2u);
v___x_2765_ = lean_mk_empty_array_with_capacity(v___x_2764_);
v___x_2766_ = lean_array_push(v___x_2765_, v_fn_2755_);
v___x_2767_ = lean_array_push(v___x_2766_, v___x_2763_);
v___x_2768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2762_);
lean_ctor_set(v___x_2768_, 1, v___x_2760_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
return v___x_2768_;
}
else
{
lean_dec_ref(v_x_2756_);
return v_fn_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* v_fn_2769_, lean_object* v_args_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = l_Lean_mkCIdent(v_fn_2769_);
v___x_2772_ = l_Lean_Syntax_mkApp(v___x_2771_, v_args_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* v_kind_2773_, lean_object* v_val_2774_, lean_object* v_info_2775_){
_start:
{
lean_object* v_atom_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_atom_2776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2776_, 0, v_info_2775_);
lean_ctor_set(v_atom_2776_, 1, v_val_2774_);
v___x_2777_ = lean_unsigned_to_nat(1u);
v___x_2778_ = lean_mk_empty_array_with_capacity(v___x_2777_);
v___x_2779_ = lean_array_push(v___x_2778_, v_atom_2776_);
v___x_2780_ = lean_box(2);
v___x_2781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v_kind_2773_);
lean_ctor_set(v___x_2781_, 2, v___x_2779_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t v_val_2785_, lean_object* v_info_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_2788_ = l_Char_quote(v_val_2785_);
v___x_2789_ = l_Lean_Syntax_mkLit(v___x_2787_, v___x_2788_, v_info_2786_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* v_val_2790_, lean_object* v_info_2791_){
_start:
{
uint32_t v_val_boxed_2792_; lean_object* v_res_2793_; 
v_val_boxed_2792_ = lean_unbox_uint32(v_val_2790_);
lean_dec(v_val_2790_);
v_res_2793_ = l_Lean_Syntax_mkCharLit(v_val_boxed_2792_, v_info_2791_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* v_val_2797_, lean_object* v_info_2798_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_2800_ = l_String_quote(v_val_2797_);
v___x_2801_ = l_Lean_Syntax_mkLit(v___x_2799_, v___x_2800_, v_info_2798_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* v_val_2805_, lean_object* v_info_2806_){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2808_ = l_Lean_Syntax_mkLit(v___x_2807_, v_val_2805_, v_info_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* v_val_2809_, lean_object* v_info_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2811_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_2812_ = l_Nat_reprFast(v_val_2809_);
v___x_2813_ = l_Lean_Syntax_mkLit(v___x_2811_, v___x_2812_, v_info_2810_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* v_val_2817_, lean_object* v_info_2818_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_2820_ = l_Lean_Syntax_mkLit(v___x_2819_, v_val_2817_, v_info_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* v_val_2824_, lean_object* v_info_2825_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_2827_ = l_Lean_Syntax_mkLit(v___x_2826_, v_val_2824_, v_info_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* v_s_2828_, lean_object* v_i_2829_, lean_object* v_val_2830_){
_start:
{
uint8_t v___x_2831_; 
v___x_2831_ = lean_string_utf8_at_end(v_s_2828_, v_i_2829_);
if (v___x_2831_ == 0)
{
uint32_t v_c_2832_; uint32_t v___x_2833_; uint8_t v___x_2834_; 
v_c_2832_ = lean_string_utf8_get(v_s_2828_, v_i_2829_);
v___x_2833_ = 48;
v___x_2834_ = lean_uint32_dec_eq(v_c_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
uint32_t v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = 49;
v___x_2836_ = lean_uint32_dec_eq(v_c_2832_, v___x_2835_);
if (v___x_2836_ == 0)
{
uint32_t v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = 95;
v___x_2838_ = lean_uint32_dec_eq(v_c_2832_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
lean_dec(v_val_2830_);
lean_dec(v_i_2829_);
v___x_2839_ = lean_box(0);
return v___x_2839_;
}
else
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_string_utf8_next(v_s_2828_, v_i_2829_);
lean_dec(v_i_2829_);
v_i_2829_ = v___x_2840_;
goto _start;
}
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2842_ = lean_string_utf8_next(v_s_2828_, v_i_2829_);
lean_dec(v_i_2829_);
v___x_2843_ = lean_unsigned_to_nat(2u);
v___x_2844_ = lean_nat_mul(v___x_2843_, v_val_2830_);
lean_dec(v_val_2830_);
v___x_2845_ = lean_unsigned_to_nat(1u);
v___x_2846_ = lean_nat_add(v___x_2844_, v___x_2845_);
lean_dec(v___x_2844_);
v_i_2829_ = v___x_2842_;
v_val_2830_ = v___x_2846_;
goto _start;
}
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_string_utf8_next(v_s_2828_, v_i_2829_);
lean_dec(v_i_2829_);
v___x_2849_ = lean_unsigned_to_nat(2u);
v___x_2850_ = lean_nat_mul(v___x_2849_, v_val_2830_);
lean_dec(v_val_2830_);
v_i_2829_ = v___x_2848_;
v_val_2830_ = v___x_2850_;
goto _start;
}
}
else
{
lean_object* v___x_2852_; 
lean_dec(v_i_2829_);
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_val_2830_);
return v___x_2852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* v_s_2853_, lean_object* v_i_2854_, lean_object* v_val_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2853_, v_i_2854_, v_val_2855_);
lean_dec_ref(v_s_2853_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* v_s_2857_, lean_object* v_i_2858_, lean_object* v_val_2859_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = lean_string_utf8_at_end(v_s_2857_, v_i_2858_);
if (v___x_2860_ == 0)
{
uint32_t v_c_2861_; uint8_t v___y_2863_; uint32_t v___x_2877_; uint8_t v___x_2878_; 
v_c_2861_ = lean_string_utf8_get(v_s_2857_, v_i_2858_);
v___x_2877_ = 48;
v___x_2878_ = lean_uint32_dec_le(v___x_2877_, v_c_2861_);
if (v___x_2878_ == 0)
{
v___y_2863_ = v___x_2860_;
goto v___jp_2862_;
}
else
{
uint32_t v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = 55;
v___x_2880_ = lean_uint32_dec_le(v_c_2861_, v___x_2879_);
v___y_2863_ = v___x_2880_;
goto v___jp_2862_;
}
v___jp_2862_:
{
if (v___y_2863_ == 0)
{
uint32_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2864_ = 95;
v___x_2865_ = lean_uint32_dec_eq(v_c_2861_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec(v_val_2859_);
lean_dec(v_i_2858_);
v___x_2866_ = lean_box(0);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_string_utf8_next(v_s_2857_, v_i_2858_);
lean_dec(v_i_2858_);
v_i_2858_ = v___x_2867_;
goto _start;
}
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2869_ = lean_string_utf8_next(v_s_2857_, v_i_2858_);
lean_dec(v_i_2858_);
v___x_2870_ = lean_unsigned_to_nat(8u);
v___x_2871_ = lean_nat_mul(v___x_2870_, v_val_2859_);
lean_dec(v_val_2859_);
v___x_2872_ = lean_uint32_to_nat(v_c_2861_);
v___x_2873_ = lean_nat_add(v___x_2871_, v___x_2872_);
lean_dec(v___x_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_unsigned_to_nat(48u);
v___x_2875_ = lean_nat_sub(v___x_2873_, v___x_2874_);
lean_dec(v___x_2873_);
v_i_2858_ = v___x_2869_;
v_val_2859_ = v___x_2875_;
goto _start;
}
}
}
else
{
lean_object* v___x_2881_; 
lean_dec(v_i_2858_);
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v_val_2859_);
return v___x_2881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* v_s_2882_, lean_object* v_i_2883_, lean_object* v_val_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2882_, v_i_2883_, v_val_2884_);
lean_dec_ref(v_s_2882_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* v_s_2886_, lean_object* v_i_2887_){
_start:
{
uint32_t v_c_2888_; lean_object* v_i_2889_; uint32_t v___x_2916_; uint8_t v___x_2917_; 
v_c_2888_ = lean_string_utf8_get(v_s_2886_, v_i_2887_);
v_i_2889_ = lean_string_utf8_next(v_s_2886_, v_i_2887_);
v___x_2916_ = 48;
v___x_2917_ = lean_uint32_dec_le(v___x_2916_, v_c_2888_);
if (v___x_2917_ == 0)
{
goto v___jp_2904_;
}
else
{
uint32_t v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = 57;
v___x_2919_ = lean_uint32_dec_le(v_c_2888_, v___x_2918_);
if (v___x_2919_ == 0)
{
goto v___jp_2904_;
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2920_ = lean_uint32_to_nat(v_c_2888_);
v___x_2921_ = lean_unsigned_to_nat(48u);
v___x_2922_ = lean_nat_sub(v___x_2920_, v___x_2921_);
lean_dec(v___x_2920_);
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v_i_2889_);
v___x_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
v___jp_2890_:
{
uint32_t v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = 65;
v___x_2892_ = lean_uint32_dec_le(v___x_2891_, v_c_2888_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; 
lean_dec(v_i_2889_);
v___x_2893_ = lean_box(0);
return v___x_2893_;
}
else
{
uint32_t v___x_2894_; uint8_t v___x_2895_; 
v___x_2894_ = 70;
v___x_2895_ = lean_uint32_dec_le(v_c_2888_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_dec(v_i_2889_);
v___x_2896_ = lean_box(0);
return v___x_2896_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2897_ = lean_unsigned_to_nat(10u);
v___x_2898_ = lean_uint32_to_nat(v_c_2888_);
v___x_2899_ = lean_nat_add(v___x_2897_, v___x_2898_);
lean_dec(v___x_2898_);
v___x_2900_ = lean_unsigned_to_nat(65u);
v___x_2901_ = lean_nat_sub(v___x_2899_, v___x_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
lean_ctor_set(v___x_2902_, 1, v_i_2889_);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
return v___x_2903_;
}
}
}
v___jp_2904_:
{
uint32_t v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = 97;
v___x_2906_ = lean_uint32_dec_le(v___x_2905_, v_c_2888_);
if (v___x_2906_ == 0)
{
goto v___jp_2890_;
}
else
{
uint32_t v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = 102;
v___x_2908_ = lean_uint32_dec_le(v_c_2888_, v___x_2907_);
if (v___x_2908_ == 0)
{
goto v___jp_2890_;
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2909_ = lean_unsigned_to_nat(10u);
v___x_2910_ = lean_uint32_to_nat(v_c_2888_);
v___x_2911_ = lean_nat_add(v___x_2909_, v___x_2910_);
lean_dec(v___x_2910_);
v___x_2912_ = lean_unsigned_to_nat(97u);
v___x_2913_ = lean_nat_sub(v___x_2911_, v___x_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v_i_2889_);
v___x_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* v_s_2925_, lean_object* v_i_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2925_, v_i_2926_);
lean_dec(v_i_2926_);
lean_dec_ref(v_s_2925_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* v_s_2928_, lean_object* v_i_2929_, lean_object* v_val_2930_){
_start:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_string_utf8_at_end(v_s_2928_, v_i_2929_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; 
v___x_2932_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_2928_, v_i_2929_);
if (lean_obj_tag(v___x_2932_) == 0)
{
uint32_t v___x_2933_; uint32_t v___x_2934_; uint8_t v___x_2935_; 
v___x_2933_ = lean_string_utf8_get(v_s_2928_, v_i_2929_);
v___x_2934_ = 95;
v___x_2935_ = lean_uint32_dec_eq(v___x_2933_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
lean_dec(v_val_2930_);
lean_dec(v_i_2929_);
v___x_2936_ = lean_box(0);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_string_utf8_next(v_s_2928_, v_i_2929_);
lean_dec(v_i_2929_);
v_i_2929_ = v___x_2937_;
goto _start;
}
}
else
{
lean_object* v_val_2939_; lean_object* v_fst_2940_; lean_object* v_snd_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
lean_dec(v_i_2929_);
v_val_2939_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_val_2939_);
lean_dec_ref_known(v___x_2932_, 1);
v_fst_2940_ = lean_ctor_get(v_val_2939_, 0);
lean_inc(v_fst_2940_);
v_snd_2941_ = lean_ctor_get(v_val_2939_, 1);
lean_inc(v_snd_2941_);
lean_dec(v_val_2939_);
v___x_2942_ = lean_unsigned_to_nat(16u);
v___x_2943_ = lean_nat_mul(v___x_2942_, v_val_2930_);
lean_dec(v_val_2930_);
v___x_2944_ = lean_nat_add(v___x_2943_, v_fst_2940_);
lean_dec(v_fst_2940_);
lean_dec(v___x_2943_);
v_i_2929_ = v_snd_2941_;
v_val_2930_ = v___x_2944_;
goto _start;
}
}
else
{
lean_object* v___x_2946_; 
lean_dec(v_i_2929_);
v___x_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_val_2930_);
return v___x_2946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* v_s_2947_, lean_object* v_i_2948_, lean_object* v_val_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_2947_, v_i_2948_, v_val_2949_);
lean_dec_ref(v_s_2947_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* v_s_2951_, lean_object* v_i_2952_, lean_object* v_val_2953_){
_start:
{
uint8_t v___x_2954_; 
v___x_2954_ = lean_string_utf8_at_end(v_s_2951_, v_i_2952_);
if (v___x_2954_ == 0)
{
uint32_t v_c_2955_; uint8_t v___y_2957_; uint32_t v___x_2971_; uint8_t v___x_2972_; 
v_c_2955_ = lean_string_utf8_get(v_s_2951_, v_i_2952_);
v___x_2971_ = 48;
v___x_2972_ = lean_uint32_dec_le(v___x_2971_, v_c_2955_);
if (v___x_2972_ == 0)
{
v___y_2957_ = v___x_2954_;
goto v___jp_2956_;
}
else
{
uint32_t v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = 57;
v___x_2974_ = lean_uint32_dec_le(v_c_2955_, v___x_2973_);
v___y_2957_ = v___x_2974_;
goto v___jp_2956_;
}
v___jp_2956_:
{
if (v___y_2957_ == 0)
{
uint32_t v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = 95;
v___x_2959_ = lean_uint32_dec_eq(v_c_2955_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; 
lean_dec(v_val_2953_);
lean_dec(v_i_2952_);
v___x_2960_ = lean_box(0);
return v___x_2960_;
}
else
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_string_utf8_next(v_s_2951_, v_i_2952_);
lean_dec(v_i_2952_);
v_i_2952_ = v___x_2961_;
goto _start;
}
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2963_ = lean_string_utf8_next(v_s_2951_, v_i_2952_);
lean_dec(v_i_2952_);
v___x_2964_ = lean_unsigned_to_nat(10u);
v___x_2965_ = lean_nat_mul(v___x_2964_, v_val_2953_);
lean_dec(v_val_2953_);
v___x_2966_ = lean_uint32_to_nat(v_c_2955_);
v___x_2967_ = lean_nat_add(v___x_2965_, v___x_2966_);
lean_dec(v___x_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_unsigned_to_nat(48u);
v___x_2969_ = lean_nat_sub(v___x_2967_, v___x_2968_);
lean_dec(v___x_2967_);
v_i_2952_ = v___x_2963_;
v_val_2953_ = v___x_2969_;
goto _start;
}
}
}
else
{
lean_object* v___x_2975_; 
lean_dec(v_i_2952_);
v___x_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_val_2953_);
return v___x_2975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* v_s_2976_, lean_object* v_i_2977_, lean_object* v_val_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_2976_, v_i_2977_, v_val_2978_);
lean_dec_ref(v_s_2976_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* v_s_2982_){
_start:
{
lean_object* v_len_2983_; lean_object* v___x_2984_; uint8_t v___x_2994_; 
v_len_2983_ = lean_string_length(v_s_2982_);
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2994_ = lean_nat_dec_eq(v_len_2983_, v___x_2984_);
if (v___x_2994_ == 0)
{
uint32_t v_c_2995_; uint32_t v___x_2996_; uint8_t v___x_2997_; 
v_c_2995_ = lean_string_utf8_get(v_s_2982_, v___x_2984_);
v___x_2996_ = 48;
v___x_2997_ = lean_uint32_dec_eq(v_c_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
uint8_t v___x_2998_; 
lean_dec(v_len_2983_);
v___x_2998_ = lean_uint32_dec_le(v___x_2996_, v_c_2995_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_box(0);
return v___x_2999_;
}
else
{
uint32_t v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = 57;
v___x_3001_ = lean_uint32_dec_le(v_c_2995_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_box(0);
return v___x_3002_;
}
else
{
lean_object* v___x_3003_; 
v___x_3003_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_2982_, v___x_2984_, v___x_2984_);
return v___x_3003_;
}
}
}
else
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = lean_nat_dec_eq(v_len_2983_, v___x_3004_);
lean_dec(v_len_2983_);
if (v___x_3005_ == 0)
{
uint32_t v_c_3006_; uint32_t v___x_3007_; uint8_t v___x_3008_; 
v_c_3006_ = lean_string_utf8_get(v_s_2982_, v___x_3004_);
v___x_3007_ = 120;
v___x_3008_ = lean_uint32_dec_eq(v_c_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
uint32_t v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = 88;
v___x_3010_ = lean_uint32_dec_eq(v_c_3006_, v___x_3009_);
if (v___x_3010_ == 0)
{
uint32_t v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = 98;
v___x_3012_ = lean_uint32_dec_eq(v_c_3006_, v___x_3011_);
if (v___x_3012_ == 0)
{
uint32_t v___x_3013_; uint8_t v___x_3014_; 
v___x_3013_ = 66;
v___x_3014_ = lean_uint32_dec_eq(v_c_3006_, v___x_3013_);
if (v___x_3014_ == 0)
{
uint32_t v___x_3015_; uint8_t v___x_3016_; 
v___x_3015_ = 111;
v___x_3016_ = lean_uint32_dec_eq(v_c_3006_, v___x_3015_);
if (v___x_3016_ == 0)
{
uint32_t v___x_3017_; uint8_t v___x_3018_; 
v___x_3017_ = 79;
v___x_3018_ = lean_uint32_dec_eq(v_c_3006_, v___x_3017_);
if (v___x_3018_ == 0)
{
uint8_t v___x_3019_; 
v___x_3019_ = lean_uint32_dec_le(v___x_2996_, v_c_3006_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_box(0);
return v___x_3020_;
}
else
{
uint32_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3021_ = 57;
v___x_3022_ = lean_uint32_dec_le(v_c_3006_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_box(0);
return v___x_3023_;
}
else
{
lean_object* v___x_3024_; 
v___x_3024_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(v_s_2982_, v___x_2984_, v___x_2984_);
return v___x_3024_;
}
}
}
else
{
goto v___jp_2985_;
}
}
else
{
goto v___jp_2985_;
}
}
else
{
goto v___jp_2988_;
}
}
else
{
goto v___jp_2988_;
}
}
else
{
goto v___jp_2991_;
}
}
else
{
goto v___jp_2991_;
}
}
else
{
lean_object* v___x_3025_; 
v___x_3025_ = ((lean_object*)(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0));
return v___x_3025_;
}
}
}
else
{
lean_object* v___x_3026_; 
lean_dec(v_len_2983_);
v___x_3026_ = lean_box(0);
return v___x_3026_;
}
v___jp_2985_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_unsigned_to_nat(2u);
v___x_2987_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(v_s_2982_, v___x_2986_, v___x_2984_);
return v___x_2987_;
}
v___jp_2988_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_unsigned_to_nat(2u);
v___x_2990_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(v_s_2982_, v___x_2989_, v___x_2984_);
return v___x_2990_;
}
v___jp_2991_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_unsigned_to_nat(2u);
v___x_2993_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_s_2982_, v___x_2992_, v___x_2984_);
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* v_s_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_s_3027_);
lean_dec_ref(v_s_3027_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* v_litKind_3029_, lean_object* v_stx_3030_){
_start:
{
if (lean_obj_tag(v_stx_3030_) == 1)
{
lean_object* v_kind_3031_; lean_object* v_args_3032_; uint8_t v___y_3034_; uint8_t v___x_3041_; 
v_kind_3031_ = lean_ctor_get(v_stx_3030_, 1);
v_args_3032_ = lean_ctor_get(v_stx_3030_, 2);
v___x_3041_ = lean_name_eq(v_kind_3031_, v_litKind_3029_);
if (v___x_3041_ == 0)
{
v___y_3034_ = v___x_3041_;
goto v___jp_3033_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3042_ = lean_array_get_size(v_args_3032_);
v___x_3043_ = lean_unsigned_to_nat(1u);
v___x_3044_ = lean_nat_dec_eq(v___x_3042_, v___x_3043_);
v___y_3034_ = v___x_3044_;
goto v___jp_3033_;
}
v___jp_3033_:
{
if (v___y_3034_ == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_box(0);
return v___x_3035_;
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = lean_array_fget_borrowed(v_args_3032_, v___x_3036_);
if (lean_obj_tag(v___x_3037_) == 2)
{
lean_object* v_val_3038_; lean_object* v___x_3039_; 
v_val_3038_ = lean_ctor_get(v___x_3037_, 1);
lean_inc_ref(v_val_3038_);
v___x_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_val_3038_);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_box(0);
return v___x_3040_;
}
}
}
}
else
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_box(0);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* v_litKind_3046_, lean_object* v_stx_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_Syntax_isLit_x3f(v_litKind_3046_, v_stx_3047_);
lean_dec(v_stx_3047_);
lean_dec(v_litKind_3046_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* v_litKind_3049_, lean_object* v_stx_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Lean_Syntax_isLit_x3f(v_litKind_3049_, v_stx_3050_);
if (lean_obj_tag(v___x_3051_) == 1)
{
lean_object* v_val_3052_; lean_object* v___x_3053_; 
v_val_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_val_3052_);
lean_dec_ref_known(v___x_3051_, 1);
v___x_3053_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_val_3052_);
lean_dec(v_val_3052_);
return v___x_3053_;
}
else
{
lean_object* v___x_3054_; 
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
return v___x_3054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* v_litKind_3055_, lean_object* v_stx_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v_litKind_3055_, v_stx_3056_);
lean_dec(v_stx_3056_);
lean_dec(v_litKind_3055_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* v_s_3058_){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
v___x_3060_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3059_, v_s_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* v_s_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_Syntax_isNatLit_x3f(v_s_3061_);
lean_dec(v_s_3061_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* v_s_3066_){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = ((lean_object*)(l_Lean_Syntax_isFieldIdx_x3f___closed__1));
v___x_3068_ = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(v___x_3067_, v_s_3066_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* v_s_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Syntax_isFieldIdx_x3f(v_s_3069_);
lean_dec(v_s_3069_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* v_s_3071_, lean_object* v_i_3072_, lean_object* v_val_3073_, lean_object* v_e_3074_, uint8_t v_sign_3075_, lean_object* v_exp_3076_){
_start:
{
uint8_t v___x_3077_; 
v___x_3077_ = lean_string_utf8_at_end(v_s_3071_, v_i_3072_);
if (v___x_3077_ == 0)
{
uint32_t v_c_3078_; uint8_t v___y_3080_; uint32_t v___x_3094_; uint8_t v___x_3095_; 
v_c_3078_ = lean_string_utf8_get(v_s_3071_, v_i_3072_);
v___x_3094_ = 48;
v___x_3095_ = lean_uint32_dec_le(v___x_3094_, v_c_3078_);
if (v___x_3095_ == 0)
{
v___y_3080_ = v___x_3077_;
goto v___jp_3079_;
}
else
{
uint32_t v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = 57;
v___x_3097_ = lean_uint32_dec_le(v_c_3078_, v___x_3096_);
v___y_3080_ = v___x_3097_;
goto v___jp_3079_;
}
v___jp_3079_:
{
if (v___y_3080_ == 0)
{
uint32_t v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = 95;
v___x_3082_ = lean_uint32_dec_eq(v_c_3078_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec(v_exp_3076_);
lean_dec(v_val_3073_);
lean_dec(v_i_3072_);
v___x_3083_ = lean_box(0);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_string_utf8_next(v_s_3071_, v_i_3072_);
lean_dec(v_i_3072_);
v_i_3072_ = v___x_3084_;
goto _start;
}
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3086_ = lean_string_utf8_next(v_s_3071_, v_i_3072_);
lean_dec(v_i_3072_);
v___x_3087_ = lean_unsigned_to_nat(10u);
v___x_3088_ = lean_nat_mul(v___x_3087_, v_exp_3076_);
lean_dec(v_exp_3076_);
v___x_3089_ = lean_uint32_to_nat(v_c_3078_);
v___x_3090_ = lean_nat_add(v___x_3088_, v___x_3089_);
lean_dec(v___x_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_unsigned_to_nat(48u);
v___x_3092_ = lean_nat_sub(v___x_3090_, v___x_3091_);
lean_dec(v___x_3090_);
v_i_3072_ = v___x_3086_;
v_exp_3076_ = v___x_3092_;
goto _start;
}
}
}
else
{
lean_dec(v_i_3072_);
if (v_sign_3075_ == 0)
{
uint8_t v___x_3098_; 
v___x_3098_ = lean_nat_dec_le(v_e_3074_, v_exp_3076_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3099_ = lean_nat_sub(v_e_3074_, v_exp_3076_);
lean_dec(v_exp_3076_);
v___x_3100_ = lean_box(v___x_3077_);
v___x_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
lean_ctor_set(v___x_3101_, 1, v___x_3099_);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_val_3073_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3104_ = lean_nat_sub(v_exp_3076_, v_e_3074_);
lean_dec(v_exp_3076_);
v___x_3105_ = lean_box(v_sign_3075_);
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3104_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v_val_3073_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3109_ = lean_nat_add(v_exp_3076_, v_e_3074_);
lean_dec(v_exp_3076_);
v___x_3110_ = lean_box(v_sign_3075_);
v___x_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v___x_3109_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_val_3073_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
return v___x_3113_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* v_s_3114_, lean_object* v_i_3115_, lean_object* v_val_3116_, lean_object* v_e_3117_, lean_object* v_sign_3118_, lean_object* v_exp_3119_){
_start:
{
uint8_t v_sign_boxed_3120_; lean_object* v_res_3121_; 
v_sign_boxed_3120_ = lean_unbox(v_sign_3118_);
v_res_3121_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3114_, v_i_3115_, v_val_3116_, v_e_3117_, v_sign_boxed_3120_, v_exp_3119_);
lean_dec(v_e_3117_);
lean_dec_ref(v_s_3114_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* v_s_3122_, lean_object* v_i_3123_, lean_object* v_val_3124_, lean_object* v_e_3125_){
_start:
{
uint8_t v___x_3126_; 
v___x_3126_ = lean_string_utf8_at_end(v_s_3122_, v_i_3123_);
if (v___x_3126_ == 0)
{
uint32_t v_c_3127_; uint32_t v___x_3128_; uint8_t v___x_3129_; 
v_c_3127_ = lean_string_utf8_get(v_s_3122_, v_i_3123_);
v___x_3128_ = 45;
v___x_3129_ = lean_uint32_dec_eq(v_c_3127_, v___x_3128_);
if (v___x_3129_ == 0)
{
uint32_t v___x_3130_; uint8_t v___x_3131_; 
v___x_3130_ = 43;
v___x_3131_ = lean_uint32_dec_eq(v_c_3127_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_unsigned_to_nat(0u);
v___x_3133_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3122_, v_i_3123_, v_val_3124_, v_e_3125_, v___x_3131_, v___x_3132_);
return v___x_3133_;
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = lean_string_utf8_next(v_s_3122_, v_i_3123_);
lean_dec(v_i_3123_);
v___x_3135_ = lean_unsigned_to_nat(0u);
v___x_3136_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3122_, v___x_3134_, v_val_3124_, v_e_3125_, v___x_3129_, v___x_3135_);
return v___x_3136_;
}
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_string_utf8_next(v_s_3122_, v_i_3123_);
lean_dec(v_i_3123_);
v___x_3138_ = lean_unsigned_to_nat(0u);
v___x_3139_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(v_s_3122_, v___x_3137_, v_val_3124_, v_e_3125_, v___x_3129_, v___x_3138_);
return v___x_3139_;
}
}
else
{
lean_object* v___x_3140_; 
lean_dec(v_val_3124_);
lean_dec(v_i_3123_);
v___x_3140_ = lean_box(0);
return v___x_3140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* v_s_3141_, lean_object* v_i_3142_, lean_object* v_val_3143_, lean_object* v_e_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3141_, v_i_3142_, v_val_3143_, v_e_3144_);
lean_dec(v_e_3144_);
lean_dec_ref(v_s_3141_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* v_s_3146_, lean_object* v_i_3147_, lean_object* v_val_3148_, lean_object* v_e_3149_){
_start:
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_string_utf8_at_end(v_s_3146_, v_i_3147_);
if (v___x_3153_ == 0)
{
uint32_t v_c_3154_; uint8_t v___y_3156_; uint32_t v___x_3176_; uint8_t v___x_3177_; 
v_c_3154_ = lean_string_utf8_get(v_s_3146_, v_i_3147_);
v___x_3176_ = 48;
v___x_3177_ = lean_uint32_dec_le(v___x_3176_, v_c_3154_);
if (v___x_3177_ == 0)
{
v___y_3156_ = v___x_3153_;
goto v___jp_3155_;
}
else
{
uint32_t v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = 57;
v___x_3179_ = lean_uint32_dec_le(v_c_3154_, v___x_3178_);
v___y_3156_ = v___x_3179_;
goto v___jp_3155_;
}
v___jp_3155_:
{
if (v___y_3156_ == 0)
{
uint32_t v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = 95;
v___x_3158_ = lean_uint32_dec_eq(v_c_3154_, v___x_3157_);
if (v___x_3158_ == 0)
{
uint32_t v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = 101;
v___x_3160_ = lean_uint32_dec_eq(v_c_3154_, v___x_3159_);
if (v___x_3160_ == 0)
{
uint32_t v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = 69;
v___x_3162_ = lean_uint32_dec_eq(v_c_3154_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
lean_dec(v_e_3149_);
lean_dec(v_val_3148_);
lean_dec(v_i_3147_);
v___x_3163_ = lean_box(0);
return v___x_3163_;
}
else
{
goto v___jp_3150_;
}
}
else
{
goto v___jp_3150_;
}
}
else
{
lean_object* v___x_3164_; 
v___x_3164_ = lean_string_utf8_next(v_s_3146_, v_i_3147_);
lean_dec(v_i_3147_);
v_i_3147_ = v___x_3164_;
goto _start;
}
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3166_ = lean_string_utf8_next(v_s_3146_, v_i_3147_);
lean_dec(v_i_3147_);
v___x_3167_ = lean_unsigned_to_nat(10u);
v___x_3168_ = lean_nat_mul(v___x_3167_, v_val_3148_);
lean_dec(v_val_3148_);
v___x_3169_ = lean_uint32_to_nat(v_c_3154_);
v___x_3170_ = lean_nat_add(v___x_3168_, v___x_3169_);
lean_dec(v___x_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_unsigned_to_nat(48u);
v___x_3172_ = lean_nat_sub(v___x_3170_, v___x_3171_);
lean_dec(v___x_3170_);
v___x_3173_ = lean_unsigned_to_nat(1u);
v___x_3174_ = lean_nat_add(v_e_3149_, v___x_3173_);
lean_dec(v_e_3149_);
v_i_3147_ = v___x_3166_;
v_val_3148_ = v___x_3172_;
v_e_3149_ = v___x_3174_;
goto _start;
}
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec(v_i_3147_);
v___x_3180_ = lean_box(v___x_3153_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v_e_3149_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_val_3148_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
v___jp_3150_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = lean_string_utf8_next(v_s_3146_, v_i_3147_);
lean_dec(v_i_3147_);
v___x_3152_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3146_, v___x_3151_, v_val_3148_, v_e_3149_);
lean_dec(v_e_3149_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* v_s_3184_, lean_object* v_i_3185_, lean_object* v_val_3186_, lean_object* v_e_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3184_, v_i_3185_, v_val_3186_, v_e_3187_);
lean_dec_ref(v_s_3184_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* v_s_3189_, lean_object* v_i_3190_, lean_object* v_val_3191_){
_start:
{
uint8_t v___x_3196_; 
v___x_3196_ = lean_string_utf8_at_end(v_s_3189_, v_i_3190_);
if (v___x_3196_ == 0)
{
uint32_t v_c_3197_; uint8_t v___y_3199_; uint32_t v___x_3222_; uint8_t v___x_3223_; 
v_c_3197_ = lean_string_utf8_get(v_s_3189_, v_i_3190_);
v___x_3222_ = 48;
v___x_3223_ = lean_uint32_dec_le(v___x_3222_, v_c_3197_);
if (v___x_3223_ == 0)
{
v___y_3199_ = v___x_3196_;
goto v___jp_3198_;
}
else
{
uint32_t v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = 57;
v___x_3225_ = lean_uint32_dec_le(v_c_3197_, v___x_3224_);
v___y_3199_ = v___x_3225_;
goto v___jp_3198_;
}
v___jp_3198_:
{
if (v___y_3199_ == 0)
{
uint32_t v___x_3200_; uint8_t v___x_3201_; 
v___x_3200_ = 95;
v___x_3201_ = lean_uint32_dec_eq(v_c_3197_, v___x_3200_);
if (v___x_3201_ == 0)
{
uint32_t v___x_3202_; uint8_t v___x_3203_; 
v___x_3202_ = 46;
v___x_3203_ = lean_uint32_dec_eq(v_c_3197_, v___x_3202_);
if (v___x_3203_ == 0)
{
uint32_t v___x_3204_; uint8_t v___x_3205_; 
v___x_3204_ = 101;
v___x_3205_ = lean_uint32_dec_eq(v_c_3197_, v___x_3204_);
if (v___x_3205_ == 0)
{
uint32_t v___x_3206_; uint8_t v___x_3207_; 
v___x_3206_ = 69;
v___x_3207_ = lean_uint32_dec_eq(v_c_3197_, v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
lean_dec(v_val_3191_);
lean_dec(v_i_3190_);
v___x_3208_ = lean_box(0);
return v___x_3208_;
}
else
{
goto v___jp_3192_;
}
}
else
{
goto v___jp_3192_;
}
}
else
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = lean_string_utf8_next(v_s_3189_, v_i_3190_);
lean_dec(v_i_3190_);
v___x_3210_ = lean_unsigned_to_nat(0u);
v___x_3211_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(v_s_3189_, v___x_3209_, v_val_3191_, v___x_3210_);
return v___x_3211_;
}
}
else
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_string_utf8_next(v_s_3189_, v_i_3190_);
lean_dec(v_i_3190_);
v_i_3190_ = v___x_3212_;
goto _start;
}
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3214_ = lean_string_utf8_next(v_s_3189_, v_i_3190_);
lean_dec(v_i_3190_);
v___x_3215_ = lean_unsigned_to_nat(10u);
v___x_3216_ = lean_nat_mul(v___x_3215_, v_val_3191_);
lean_dec(v_val_3191_);
v___x_3217_ = lean_uint32_to_nat(v_c_3197_);
v___x_3218_ = lean_nat_add(v___x_3216_, v___x_3217_);
lean_dec(v___x_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_unsigned_to_nat(48u);
v___x_3220_ = lean_nat_sub(v___x_3218_, v___x_3219_);
lean_dec(v___x_3218_);
v_i_3190_ = v___x_3214_;
v_val_3191_ = v___x_3220_;
goto _start;
}
}
}
else
{
lean_object* v___x_3226_; 
lean_dec(v_val_3191_);
lean_dec(v_i_3190_);
v___x_3226_ = lean_box(0);
return v___x_3226_;
}
v___jp_3192_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_string_utf8_next(v_s_3189_, v_i_3190_);
lean_dec(v_i_3190_);
v___x_3194_ = lean_unsigned_to_nat(0u);
v___x_3195_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(v_s_3189_, v___x_3193_, v_val_3191_, v___x_3194_);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* v_s_3227_, lean_object* v_i_3228_, lean_object* v_val_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3227_, v_i_3228_, v_val_3229_);
lean_dec_ref(v_s_3227_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* v_s_3231_){
_start:
{
lean_object* v_len_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_len_3232_ = lean_string_length(v_s_3231_);
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = lean_nat_dec_eq(v_len_3232_, v___x_3233_);
lean_dec(v_len_3232_);
if (v___x_3234_ == 0)
{
uint32_t v_c_3235_; uint32_t v___x_3236_; uint8_t v___x_3237_; 
v_c_3235_ = lean_string_utf8_get(v_s_3231_, v___x_3233_);
v___x_3236_ = 48;
v___x_3237_ = lean_uint32_dec_le(v___x_3236_, v_c_3235_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_box(0);
return v___x_3238_;
}
else
{
uint32_t v___x_3239_; uint8_t v___x_3240_; 
v___x_3239_ = 57;
v___x_3240_ = lean_uint32_dec_le(v_c_3235_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_box(0);
return v___x_3241_;
}
else
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(v_s_3231_, v___x_3233_, v___x_3233_);
return v___x_3242_;
}
}
}
else
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_box(0);
return v___x_3243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* v_s_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_s_3244_);
lean_dec_ref(v_s_3244_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* v_stx_3246_){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = ((lean_object*)(l_Lean_Syntax_mkScientificLit___closed__1));
v___x_3248_ = l_Lean_Syntax_isLit_x3f(v___x_3247_, v_stx_3246_);
if (lean_obj_tag(v___x_3248_) == 1)
{
lean_object* v_val_3249_; lean_object* v___x_3250_; 
v_val_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_val_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v_val_3249_);
lean_dec(v_val_3249_);
return v___x_3250_;
}
else
{
lean_object* v___x_3251_; 
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
return v___x_3251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* v_stx_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_Syntax_isScientificLit_x3f(v_stx_3252_);
lean_dec(v_stx_3252_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* v_x_3254_){
_start:
{
switch(lean_obj_tag(v_x_3254_))
{
case 2:
{
lean_object* v_val_3255_; lean_object* v___x_3256_; 
v_val_3255_ = lean_ctor_get(v_x_3254_, 1);
lean_inc_ref(v_val_3255_);
lean_dec_ref_known(v_x_3254_, 2);
v___x_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_val_3255_);
return v___x_3256_;
}
case 3:
{
lean_object* v_rawVal_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_rawVal_3257_ = lean_ctor_get(v_x_3254_, 1);
lean_inc_ref(v_rawVal_3257_);
lean_dec_ref_known(v_x_3254_, 4);
v___x_3258_ = lean_substring_tostring(v_rawVal_3257_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
return v___x_3259_;
}
default: 
{
lean_object* v___x_3260_; 
lean_dec(v_x_3254_);
v___x_3260_ = lean_box(0);
return v___x_3260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* v_stx_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_Syntax_isNatLit_x3f(v_stx_3261_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_unsigned_to_nat(0u);
return v___x_3263_;
}
else
{
lean_object* v_val_3264_; 
v_val_3264_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_val_3264_);
lean_dec_ref_known(v___x_3262_, 1);
return v_val_3264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* v_stx_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_Syntax_toNat(v_stx_3265_);
lean_dec(v_stx_3265_);
return v_res_3266_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = 9;
v___x_3268_ = lean_box_uint32(v___x_3267_);
return v___x_3268_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2(void){
_start:
{
uint32_t v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = 10;
v___x_3270_ = lean_box_uint32(v___x_3269_);
return v___x_3270_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3(void){
_start:
{
uint32_t v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = 13;
v___x_3272_ = lean_box_uint32(v___x_3271_);
return v___x_3272_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4(void){
_start:
{
uint32_t v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = 39;
v___x_3274_ = lean_box_uint32(v___x_3273_);
return v___x_3274_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5(void){
_start:
{
uint32_t v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = 34;
v___x_3276_ = lean_box_uint32(v___x_3275_);
return v___x_3276_;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6(void){
_start:
{
uint32_t v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = 92;
v___x_3278_ = lean_box_uint32(v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* v_s_3279_, lean_object* v_i_3280_){
_start:
{
uint32_t v_c_3281_; lean_object* v_i_3282_; uint32_t v___x_3283_; uint8_t v___x_3284_; 
v_c_3281_ = lean_string_utf8_get(v_s_3279_, v_i_3280_);
v_i_3282_ = lean_string_utf8_next(v_s_3279_, v_i_3280_);
v___x_3283_ = 92;
v___x_3284_ = lean_uint32_dec_eq(v_c_3281_, v___x_3283_);
if (v___x_3284_ == 0)
{
uint32_t v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = 34;
v___x_3286_ = lean_uint32_dec_eq(v_c_3281_, v___x_3285_);
if (v___x_3286_ == 0)
{
uint32_t v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = 39;
v___x_3288_ = lean_uint32_dec_eq(v_c_3281_, v___x_3287_);
if (v___x_3288_ == 0)
{
uint32_t v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = 114;
v___x_3290_ = lean_uint32_dec_eq(v_c_3281_, v___x_3289_);
if (v___x_3290_ == 0)
{
uint32_t v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = 110;
v___x_3292_ = lean_uint32_dec_eq(v_c_3281_, v___x_3291_);
if (v___x_3292_ == 0)
{
uint32_t v___x_3293_; uint8_t v___x_3294_; 
v___x_3293_ = 116;
v___x_3294_ = lean_uint32_dec_eq(v_c_3281_, v___x_3293_);
if (v___x_3294_ == 0)
{
uint32_t v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = 120;
v___x_3296_ = lean_uint32_dec_eq(v_c_3281_, v___x_3295_);
if (v___x_3296_ == 0)
{
uint32_t v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = 117;
v___x_3298_ = lean_uint32_dec_eq(v_c_3281_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; 
lean_dec(v_i_3282_);
v___x_3299_ = lean_box(0);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3279_, v_i_3282_);
lean_dec(v_i_3282_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_box(0);
return v___x_3301_;
}
else
{
lean_object* v_val_3302_; lean_object* v_fst_3303_; lean_object* v_snd_3304_; lean_object* v___x_3305_; 
v_val_3302_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v___x_3300_, 1);
v_fst_3303_ = lean_ctor_get(v_val_3302_, 0);
lean_inc(v_fst_3303_);
v_snd_3304_ = lean_ctor_get(v_val_3302_, 1);
lean_inc(v_snd_3304_);
lean_dec(v_val_3302_);
v___x_3305_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3279_, v_snd_3304_);
lean_dec(v_snd_3304_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v___x_3306_; 
lean_dec(v_fst_3303_);
v___x_3306_ = lean_box(0);
return v___x_3306_;
}
else
{
lean_object* v_val_3307_; lean_object* v_fst_3308_; lean_object* v_snd_3309_; lean_object* v___x_3310_; 
v_val_3307_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_val_3307_);
lean_dec_ref_known(v___x_3305_, 1);
v_fst_3308_ = lean_ctor_get(v_val_3307_, 0);
lean_inc(v_fst_3308_);
v_snd_3309_ = lean_ctor_get(v_val_3307_, 1);
lean_inc(v_snd_3309_);
lean_dec(v_val_3307_);
v___x_3310_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3279_, v_snd_3309_);
lean_dec(v_snd_3309_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v___x_3311_; 
lean_dec(v_fst_3308_);
lean_dec(v_fst_3303_);
v___x_3311_ = lean_box(0);
return v___x_3311_;
}
else
{
lean_object* v_val_3312_; lean_object* v_fst_3313_; lean_object* v_snd_3314_; lean_object* v___x_3315_; 
v_val_3312_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_val_3312_);
lean_dec_ref_known(v___x_3310_, 1);
v_fst_3313_ = lean_ctor_get(v_val_3312_, 0);
lean_inc(v_fst_3313_);
v_snd_3314_ = lean_ctor_get(v_val_3312_, 1);
lean_inc(v_snd_3314_);
lean_dec(v_val_3312_);
v___x_3315_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3279_, v_snd_3314_);
lean_dec(v_snd_3314_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v___x_3316_; 
lean_dec(v_fst_3313_);
lean_dec(v_fst_3308_);
lean_dec(v_fst_3303_);
v___x_3316_ = lean_box(0);
return v___x_3316_;
}
else
{
lean_object* v_val_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3342_; 
v_val_3317_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3319_ = v___x_3315_;
v_isShared_3320_ = v_isSharedCheck_3342_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_val_3317_);
lean_dec(v___x_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3342_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3341_; 
v_fst_3321_ = lean_ctor_get(v_val_3317_, 0);
v_snd_3322_ = lean_ctor_get(v_val_3317_, 1);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_val_3317_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3324_ = v_val_3317_;
v_isShared_3325_ = v_isSharedCheck_3341_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_snd_3322_);
lean_inc(v_fst_3321_);
lean_dec(v_val_3317_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3341_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint32_t v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3326_ = lean_unsigned_to_nat(16u);
v___x_3327_ = lean_nat_mul(v___x_3326_, v_fst_3303_);
lean_dec(v_fst_3303_);
v___x_3328_ = lean_nat_add(v___x_3327_, v_fst_3308_);
lean_dec(v_fst_3308_);
lean_dec(v___x_3327_);
v___x_3329_ = lean_nat_mul(v___x_3326_, v___x_3328_);
lean_dec(v___x_3328_);
v___x_3330_ = lean_nat_add(v___x_3329_, v_fst_3313_);
lean_dec(v_fst_3313_);
lean_dec(v___x_3329_);
v___x_3331_ = lean_nat_mul(v___x_3326_, v___x_3330_);
lean_dec(v___x_3330_);
v___x_3332_ = lean_nat_add(v___x_3331_, v_fst_3321_);
lean_dec(v_fst_3321_);
lean_dec(v___x_3331_);
v___x_3333_ = l_Char_ofNat(v___x_3332_);
lean_dec(v___x_3332_);
v___x_3334_ = lean_box_uint32(v___x_3333_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3334_);
v___x_3336_ = v___x_3324_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_snd_3322_);
v___x_3336_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v___x_3336_);
v___x_3338_ = v___x_3319_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
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
else
{
lean_object* v___x_3343_; 
v___x_3343_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3279_, v_i_3282_);
lean_dec(v_i_3282_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_box(0);
return v___x_3344_;
}
else
{
lean_object* v_val_3345_; lean_object* v_fst_3346_; lean_object* v_snd_3347_; lean_object* v___x_3348_; 
v_val_3345_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v___x_3343_, 1);
v_fst_3346_ = lean_ctor_get(v_val_3345_, 0);
lean_inc(v_fst_3346_);
v_snd_3347_ = lean_ctor_get(v_val_3345_, 1);
lean_inc(v_snd_3347_);
lean_dec(v_val_3345_);
v___x_3348_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(v_s_3279_, v_snd_3347_);
lean_dec(v_snd_3347_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v___x_3349_; 
lean_dec(v_fst_3346_);
v___x_3349_ = lean_box(0);
return v___x_3349_;
}
else
{
lean_object* v_val_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3371_; 
v_val_3350_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3352_ = v___x_3348_;
v_isShared_3353_ = v_isSharedCheck_3371_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_val_3350_);
lean_dec(v___x_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3371_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_fst_3354_; lean_object* v_snd_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3370_; 
v_fst_3354_ = lean_ctor_get(v_val_3350_, 0);
v_snd_3355_ = lean_ctor_get(v_val_3350_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_val_3350_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3357_ = v_val_3350_;
v_isShared_3358_ = v_isSharedCheck_3370_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_snd_3355_);
lean_inc(v_fst_3354_);
lean_dec(v_val_3350_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3370_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint32_t v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3359_ = lean_unsigned_to_nat(16u);
v___x_3360_ = lean_nat_mul(v___x_3359_, v_fst_3346_);
lean_dec(v_fst_3346_);
v___x_3361_ = lean_nat_add(v___x_3360_, v_fst_3354_);
lean_dec(v_fst_3354_);
lean_dec(v___x_3360_);
v___x_3362_ = l_Char_ofNat(v___x_3361_);
lean_dec(v___x_3361_);
v___x_3363_ = lean_box_uint32(v___x_3362_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3363_);
v___x_3365_ = v___x_3357_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_snd_3355_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3365_);
v___x_3367_ = v___x_3352_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3372_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
lean_ctor_set(v___x_3373_, 1, v_i_3282_);
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
return v___x_3374_;
}
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3375_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
lean_ctor_set(v___x_3376_, 1, v_i_3282_);
v___x_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
return v___x_3377_;
}
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3378_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v_i_3282_);
v___x_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
return v___x_3380_;
}
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
lean_ctor_set(v___x_3382_, 1, v_i_3282_);
v___x_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
return v___x_3383_;
}
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
lean_ctor_set(v___x_3385_, 1, v_i_3282_);
v___x_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
return v___x_3386_;
}
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v_i_3282_);
v___x_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
return v___x_3389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* v_s_3390_, lean_object* v_i_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Syntax_decodeQuotedChar(v_s_3390_, v_i_3391_);
lean_dec(v_i_3391_);
lean_dec_ref(v_s_3390_);
return v_res_3392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t v___y_3393_){
_start:
{
uint32_t v___x_3394_; uint8_t v___x_3395_; 
v___x_3394_ = 32;
v___x_3395_ = lean_uint32_dec_eq(v___y_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
uint32_t v___x_3396_; uint8_t v___x_3397_; 
v___x_3396_ = 9;
v___x_3397_ = lean_uint32_dec_eq(v___y_3393_, v___x_3396_);
if (v___x_3397_ == 0)
{
uint32_t v___x_3398_; uint8_t v___x_3399_; 
v___x_3398_ = 13;
v___x_3399_ = lean_uint32_dec_eq(v___y_3393_, v___x_3398_);
if (v___x_3399_ == 0)
{
uint32_t v___x_3400_; uint8_t v___x_3401_; 
v___x_3400_ = 10;
v___x_3401_ = lean_uint32_dec_eq(v___y_3393_, v___x_3400_);
return v___x_3401_;
}
else
{
return v___x_3399_;
}
}
else
{
return v___x_3397_;
}
}
else
{
return v___x_3395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* v___y_3402_){
_start:
{
uint32_t v___y_264__boxed_3403_; uint8_t v_res_3404_; lean_object* v_r_3405_; 
v___y_264__boxed_3403_ = lean_unbox_uint32(v___y_3402_);
lean_dec(v___y_3402_);
v_res_3404_ = l_Lean_Syntax_decodeStringGap___lam__0(v___y_264__boxed_3403_);
v_r_3405_ = lean_box(v_res_3404_);
return v_r_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* v_s_3407_, lean_object* v_i_3408_){
_start:
{
lean_object* v___f_3409_; uint32_t v___x_3414_; uint32_t v___x_3415_; uint8_t v___x_3416_; 
v___f_3409_ = ((lean_object*)(l_Lean_Syntax_decodeStringGap___closed__0));
v___x_3414_ = lean_string_utf8_get(v_s_3407_, v_i_3408_);
v___x_3415_ = 32;
v___x_3416_ = lean_uint32_dec_eq(v___x_3414_, v___x_3415_);
if (v___x_3416_ == 0)
{
uint32_t v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = 9;
v___x_3418_ = lean_uint32_dec_eq(v___x_3414_, v___x_3417_);
if (v___x_3418_ == 0)
{
uint32_t v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = 13;
v___x_3420_ = lean_uint32_dec_eq(v___x_3414_, v___x_3419_);
if (v___x_3420_ == 0)
{
uint32_t v___x_3421_; uint8_t v___x_3422_; 
v___x_3421_ = 10;
v___x_3422_ = lean_uint32_dec_eq(v___x_3414_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; 
lean_dec_ref(v_s_3407_);
v___x_3423_ = lean_box(0);
return v___x_3423_;
}
else
{
goto v___jp_3410_;
}
}
else
{
goto v___jp_3410_;
}
}
else
{
goto v___jp_3410_;
}
}
else
{
goto v___jp_3410_;
}
v___jp_3410_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3411_ = lean_string_utf8_next(v_s_3407_, v_i_3408_);
v___x_3412_ = lean_string_nextwhile(v_s_3407_, v___f_3409_, v___x_3411_);
v___x_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
return v___x_3413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* v_s_3424_, lean_object* v_i_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lean_Syntax_decodeStringGap(v_s_3424_, v_i_3425_);
lean_dec(v_i_3425_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* v_s_3427_, lean_object* v_i_3428_, lean_object* v_acc_3429_){
_start:
{
uint32_t v_c_3430_; uint32_t v___x_3431_; uint8_t v___x_3432_; 
v_c_3430_ = lean_string_utf8_get(v_s_3427_, v_i_3428_);
v___x_3431_ = 34;
v___x_3432_ = lean_uint32_dec_eq(v_c_3430_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_object* v_i_3433_; uint8_t v___x_3434_; 
v_i_3433_ = lean_string_utf8_next(v_s_3427_, v_i_3428_);
lean_dec(v_i_3428_);
v___x_3434_ = lean_string_utf8_at_end(v_s_3427_, v_i_3433_);
if (v___x_3434_ == 0)
{
uint32_t v___x_3435_; uint8_t v___x_3436_; 
v___x_3435_ = 92;
v___x_3436_ = lean_uint32_dec_eq(v_c_3430_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_string_push(v_acc_3429_, v_c_3430_);
v_i_3428_ = v_i_3433_;
v_acc_3429_ = v___x_3437_;
goto _start;
}
else
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Syntax_decodeQuotedChar(v_s_3427_, v_i_3433_);
if (lean_obj_tag(v___x_3439_) == 1)
{
lean_object* v_val_3440_; lean_object* v_fst_3441_; lean_object* v_snd_3442_; uint32_t v___x_3443_; lean_object* v___x_3444_; 
lean_dec(v_i_3433_);
v_val_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_val_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v_fst_3441_ = lean_ctor_get(v_val_3440_, 0);
lean_inc(v_fst_3441_);
v_snd_3442_ = lean_ctor_get(v_val_3440_, 1);
lean_inc(v_snd_3442_);
lean_dec(v_val_3440_);
v___x_3443_ = lean_unbox_uint32(v_fst_3441_);
lean_dec(v_fst_3441_);
v___x_3444_ = lean_string_push(v_acc_3429_, v___x_3443_);
v_i_3428_ = v_snd_3442_;
v_acc_3429_ = v___x_3444_;
goto _start;
}
else
{
lean_object* v___x_3446_; 
lean_dec(v___x_3439_);
lean_inc_ref(v_s_3427_);
v___x_3446_ = l_Lean_Syntax_decodeStringGap(v_s_3427_, v_i_3433_);
lean_dec(v_i_3433_);
if (lean_obj_tag(v___x_3446_) == 1)
{
lean_object* v_val_3447_; 
v_val_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_val_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v_i_3428_ = v_val_3447_;
goto _start;
}
else
{
lean_object* v___x_3449_; 
lean_dec(v___x_3446_);
lean_dec_ref(v_acc_3429_);
lean_dec_ref(v_s_3427_);
v___x_3449_ = lean_box(0);
return v___x_3449_;
}
}
}
}
else
{
lean_object* v___x_3450_; 
lean_dec(v_i_3433_);
lean_dec_ref(v_acc_3429_);
lean_dec_ref(v_s_3427_);
v___x_3450_ = lean_box(0);
return v___x_3450_;
}
}
else
{
lean_object* v___x_3451_; 
lean_dec(v_i_3428_);
lean_dec_ref(v_s_3427_);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_acc_3429_);
return v___x_3451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* v_s_3452_, lean_object* v_i_3453_, lean_object* v_num_3454_){
_start:
{
uint32_t v_c_3455_; lean_object* v_i_3456_; uint32_t v___x_3457_; uint8_t v___x_3458_; 
v_c_3455_ = lean_string_utf8_get(v_s_3452_, v_i_3453_);
v_i_3456_ = lean_string_utf8_next(v_s_3452_, v_i_3453_);
lean_dec(v_i_3453_);
v___x_3457_ = 35;
v___x_3458_ = lean_uint32_dec_eq(v_c_3455_, v___x_3457_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3459_ = lean_string_utf8_byte_size(v_s_3452_);
v___x_3460_ = lean_unsigned_to_nat(1u);
v___x_3461_ = lean_nat_add(v_num_3454_, v___x_3460_);
lean_dec(v_num_3454_);
v___x_3462_ = lean_nat_sub(v___x_3459_, v___x_3461_);
lean_dec(v___x_3461_);
v___x_3463_ = lean_string_utf8_extract(v_s_3452_, v_i_3456_, v___x_3462_);
lean_dec(v___x_3462_);
lean_dec(v_i_3456_);
return v___x_3463_;
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = lean_unsigned_to_nat(1u);
v___x_3465_ = lean_nat_add(v_num_3454_, v___x_3464_);
lean_dec(v_num_3454_);
v_i_3453_ = v_i_3456_;
v_num_3454_ = v___x_3465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* v_s_3467_, lean_object* v_i_3468_, lean_object* v_num_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3467_, v_i_3468_, v_num_3469_);
lean_dec_ref(v_s_3467_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* v_s_3471_){
_start:
{
lean_object* v___x_3472_; uint32_t v___x_3473_; uint32_t v___x_3474_; uint8_t v___x_3475_; 
v___x_3472_ = lean_unsigned_to_nat(0u);
v___x_3473_ = lean_string_utf8_get(v_s_3471_, v___x_3472_);
v___x_3474_ = 114;
v___x_3475_ = lean_uint32_dec_eq(v___x_3473_, v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = lean_unsigned_to_nat(1u);
v___x_3477_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_3478_ = l_Lean_Syntax_decodeStrLitAux(v_s_3471_, v___x_3476_, v___x_3477_);
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3479_ = lean_unsigned_to_nat(1u);
v___x_3480_ = l_Lean_Syntax_decodeRawStrLitAux(v_s_3471_, v___x_3479_, v___x_3472_);
lean_dec_ref(v_s_3471_);
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* v_stx_3482_){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_Syntax_mkStrLit___closed__1));
v___x_3484_ = l_Lean_Syntax_isLit_x3f(v___x_3483_, v_stx_3482_);
if (lean_obj_tag(v___x_3484_) == 1)
{
lean_object* v_val_3485_; lean_object* v___x_3486_; 
v_val_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_val_3485_);
lean_dec_ref_known(v___x_3484_, 1);
v___x_3486_ = l_Lean_Syntax_decodeStrLit(v_val_3485_);
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; 
lean_dec(v___x_3484_);
v___x_3487_ = lean_box(0);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* v_stx_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Syntax_isStrLit_x3f(v_stx_3488_);
lean_dec(v_stx_3488_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* v_s_3490_){
_start:
{
lean_object* v___x_3491_; uint32_t v_c_3492_; uint32_t v___x_3493_; uint8_t v___x_3494_; 
v___x_3491_ = lean_unsigned_to_nat(1u);
v_c_3492_ = lean_string_utf8_get(v_s_3490_, v___x_3491_);
v___x_3493_ = 92;
v___x_3494_ = lean_uint32_dec_eq(v_c_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = lean_box_uint32(v_c_3492_);
v___x_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
return v___x_3496_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = lean_unsigned_to_nat(2u);
v___x_3498_ = l_Lean_Syntax_decodeQuotedChar(v_s_3490_, v___x_3497_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_box(0);
return v___x_3499_;
}
else
{
lean_object* v_val_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3508_; 
v_val_3500_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3502_ = v___x_3498_;
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_val_3500_);
lean_dec(v___x_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_fst_3504_; lean_object* v___x_3506_; 
v_fst_3504_ = lean_ctor_get(v_val_3500_, 0);
lean_inc(v_fst_3504_);
lean_dec(v_val_3500_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v_fst_3504_);
v___x_3506_ = v___x_3502_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_fst_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* v_s_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_Syntax_decodeCharLit(v_s_3509_);
lean_dec_ref(v_s_3509_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* v_stx_3511_){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = ((lean_object*)(l_Lean_Syntax_mkCharLit___closed__1));
v___x_3513_ = l_Lean_Syntax_isLit_x3f(v___x_3512_, v_stx_3511_);
if (lean_obj_tag(v___x_3513_) == 1)
{
lean_object* v_val_3514_; lean_object* v___x_3515_; 
v_val_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_val_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = l_Lean_Syntax_decodeCharLit(v_val_3514_);
lean_dec(v_val_3514_);
return v___x_3515_;
}
else
{
lean_object* v___x_3516_; 
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
return v___x_3516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* v_stx_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_Syntax_isCharLit_x3f(v_stx_3517_);
lean_dec(v_stx_3517_);
return v_res_3518_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t v___y_3519_){
_start:
{
uint8_t v___y_3537_; uint32_t v___x_3542_; uint8_t v___x_3543_; 
v___x_3542_ = 65;
v___x_3543_ = lean_uint32_dec_le(v___x_3542_, v___y_3519_);
if (v___x_3543_ == 0)
{
v___y_3537_ = v___x_3543_;
goto v___jp_3536_;
}
else
{
uint32_t v___x_3544_; uint8_t v___x_3545_; 
v___x_3544_ = 90;
v___x_3545_ = lean_uint32_dec_le(v___y_3519_, v___x_3544_);
v___y_3537_ = v___x_3545_;
goto v___jp_3536_;
}
v___jp_3520_:
{
uint32_t v___x_3521_; uint8_t v___x_3522_; 
v___x_3521_ = 95;
v___x_3522_ = lean_uint32_dec_eq(v___y_3519_, v___x_3521_);
if (v___x_3522_ == 0)
{
uint32_t v___x_3523_; uint8_t v___x_3524_; 
v___x_3523_ = 39;
v___x_3524_ = lean_uint32_dec_eq(v___y_3519_, v___x_3523_);
if (v___x_3524_ == 0)
{
uint32_t v___x_3525_; uint8_t v___x_3526_; 
v___x_3525_ = 33;
v___x_3526_ = lean_uint32_dec_eq(v___y_3519_, v___x_3525_);
if (v___x_3526_ == 0)
{
uint32_t v___x_3527_; uint8_t v___x_3528_; 
v___x_3527_ = 63;
v___x_3528_ = lean_uint32_dec_eq(v___y_3519_, v___x_3527_);
if (v___x_3528_ == 0)
{
uint8_t v___x_3529_; 
v___x_3529_ = l_Lean_isLetterLike(v___y_3519_);
if (v___x_3529_ == 0)
{
uint8_t v___x_3530_; 
v___x_3530_ = l_Lean_isSubScriptAlnum(v___y_3519_);
return v___x_3530_;
}
else
{
return v___x_3529_;
}
}
else
{
return v___x_3528_;
}
}
else
{
return v___x_3526_;
}
}
else
{
return v___x_3524_;
}
}
else
{
return v___x_3522_;
}
}
v___jp_3531_:
{
uint32_t v___x_3532_; uint8_t v___x_3533_; 
v___x_3532_ = 48;
v___x_3533_ = lean_uint32_dec_le(v___x_3532_, v___y_3519_);
if (v___x_3533_ == 0)
{
goto v___jp_3520_;
}
else
{
uint32_t v___x_3534_; uint8_t v___x_3535_; 
v___x_3534_ = 57;
v___x_3535_ = lean_uint32_dec_le(v___y_3519_, v___x_3534_);
if (v___x_3535_ == 0)
{
goto v___jp_3520_;
}
else
{
return v___x_3535_;
}
}
}
v___jp_3536_:
{
if (v___y_3537_ == 0)
{
uint32_t v___x_3538_; uint8_t v___x_3539_; 
v___x_3538_ = 97;
v___x_3539_ = lean_uint32_dec_le(v___x_3538_, v___y_3519_);
if (v___x_3539_ == 0)
{
goto v___jp_3531_;
}
else
{
uint32_t v___x_3540_; uint8_t v___x_3541_; 
v___x_3540_ = 122;
v___x_3541_ = lean_uint32_dec_le(v___y_3519_, v___x_3540_);
if (v___x_3541_ == 0)
{
goto v___jp_3531_;
}
else
{
return v___x_3541_;
}
}
}
else
{
return v___y_3537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* v___y_3546_){
_start:
{
uint32_t v___y_509__boxed_3547_; uint8_t v_res_3548_; lean_object* v_r_3549_; 
v___y_509__boxed_3547_ = lean_unbox_uint32(v___y_3546_);
lean_dec(v___y_3546_);
v_res_3548_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(v___y_509__boxed_3547_);
v_r_3549_ = lean_box(v_res_3548_);
return v_r_3549_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t v___x_3550_, uint32_t v___x_3551_, uint32_t v___y_3552_){
_start:
{
uint8_t v___x_3553_; 
v___x_3553_ = lean_uint32_dec_le(v___x_3550_, v___y_3552_);
if (v___x_3553_ == 0)
{
return v___x_3553_;
}
else
{
uint8_t v___x_3554_; 
v___x_3554_ = lean_uint32_dec_le(v___y_3552_, v___x_3551_);
return v___x_3554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* v___x_3555_, lean_object* v___x_3556_, lean_object* v___y_3557_){
_start:
{
uint32_t v___x_564__boxed_3558_; uint32_t v___x_565__boxed_3559_; uint32_t v___y_566__boxed_3560_; uint8_t v_res_3561_; lean_object* v_r_3562_; 
v___x_564__boxed_3558_ = lean_unbox_uint32(v___x_3555_);
lean_dec(v___x_3555_);
v___x_565__boxed_3559_ = lean_unbox_uint32(v___x_3556_);
lean_dec(v___x_3556_);
v___y_566__boxed_3560_ = lean_unbox_uint32(v___y_3557_);
lean_dec(v___y_3557_);
v_res_3561_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(v___x_564__boxed_3558_, v___x_565__boxed_3559_, v___y_566__boxed_3560_);
v_r_3562_ = lean_box(v_res_3561_);
return v_r_3562_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t v___x_3563_, uint8_t v___x_3564_, uint32_t v_x_3565_){
_start:
{
uint32_t v___x_3566_; uint8_t v___x_3567_; 
v___x_3566_ = 187;
v___x_3567_ = lean_uint32_dec_eq(v_x_3565_, v___x_3566_);
if (v___x_3567_ == 0)
{
return v___x_3563_;
}
else
{
return v___x_3564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* v___x_3568_, lean_object* v___x_3569_, lean_object* v_x_3570_){
_start:
{
uint8_t v___x_577__boxed_3571_; uint8_t v___x_578__boxed_3572_; uint32_t v_x_579__boxed_3573_; uint8_t v_res_3574_; lean_object* v_r_3575_; 
v___x_577__boxed_3571_ = lean_unbox(v___x_3568_);
v___x_578__boxed_3572_ = lean_unbox(v___x_3569_);
v_x_579__boxed_3573_ = lean_unbox_uint32(v_x_3570_);
lean_dec(v_x_3570_);
v_res_3574_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(v___x_577__boxed_3571_, v___x_578__boxed_3572_, v_x_579__boxed_3573_);
v_r_3575_ = lean_box(v_res_3574_);
return v_r_3575_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = 48;
v___x_3578_ = lean_box_uint32(v___x_3577_);
return v___x_3578_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2(void){
_start:
{
uint32_t v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = 57;
v___x_3580_ = lean_box_uint32(v___x_3579_);
return v___x_3580_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___f_3583_; 
v___x_3581_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1;
v___x_3582_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2;
v___f_3583_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3583_, 0, v___x_3581_);
lean_closure_set(v___f_3583_, 1, v___x_3582_);
return v___f_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* v_ss_3584_, lean_object* v_acc_3585_){
_start:
{
lean_object* v_ss_3587_; lean_object* v_acc_3588_; uint8_t v___x_3597_; 
lean_inc_ref(v_ss_3584_);
v___x_3597_ = lean_substring_isempty(v_ss_3584_);
if (v___x_3597_ == 0)
{
uint32_t v_curr_3598_; uint32_t v___x_3599_; uint8_t v___x_3600_; 
lean_inc_ref(v_ss_3584_);
v_curr_3598_ = lean_substring_front(v_ss_3584_);
v___x_3599_ = 171;
v___x_3600_ = lean_uint32_dec_eq(v_curr_3598_, v___x_3599_);
if (v___x_3600_ == 0)
{
lean_object* v___f_3601_; uint8_t v___y_3633_; uint32_t v___x_3638_; uint8_t v___x_3639_; 
v___f_3601_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0));
v___x_3638_ = 65;
v___x_3639_ = lean_uint32_dec_le(v___x_3638_, v_curr_3598_);
if (v___x_3639_ == 0)
{
v___y_3633_ = v___x_3639_;
goto v___jp_3632_;
}
else
{
uint32_t v___x_3640_; uint8_t v___x_3641_; 
v___x_3640_ = 90;
v___x_3641_ = lean_uint32_dec_le(v_curr_3598_, v___x_3640_);
v___y_3633_ = v___x_3641_;
goto v___jp_3632_;
}
v___jp_3602_:
{
lean_object* v_idPart_3603_; lean_object* v_startPos_3604_; lean_object* v_stopPos_3605_; lean_object* v_startPos_3606_; lean_object* v_stopPos_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_inc_ref(v_ss_3584_);
v_idPart_3603_ = lean_substring_takewhile(v_ss_3584_, v___f_3601_);
v_startPos_3604_ = lean_ctor_get(v_idPart_3603_, 1);
lean_inc(v_startPos_3604_);
v_stopPos_3605_ = lean_ctor_get(v_idPart_3603_, 2);
lean_inc(v_stopPos_3605_);
v_startPos_3606_ = lean_ctor_get(v_ss_3584_, 1);
v_stopPos_3607_ = lean_ctor_get(v_ss_3584_, 2);
v___x_3608_ = lean_nat_sub(v_stopPos_3605_, v_startPos_3604_);
lean_dec(v_startPos_3604_);
lean_dec(v_stopPos_3605_);
v___x_3609_ = lean_nat_sub(v_stopPos_3607_, v_startPos_3606_);
v___x_3610_ = lean_substring_extract(v_ss_3584_, v___x_3608_, v___x_3609_);
v___x_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_idPart_3603_);
lean_ctor_set(v___x_3611_, 1, v_acc_3585_);
v_ss_3587_ = v___x_3610_;
v_acc_3588_ = v___x_3611_;
goto v___jp_3586_;
}
v___jp_3612_:
{
uint32_t v___x_3613_; uint8_t v___x_3614_; 
v___x_3613_ = 95;
v___x_3614_ = lean_uint32_dec_eq(v_curr_3598_, v___x_3613_);
if (v___x_3614_ == 0)
{
uint8_t v___x_3615_; 
v___x_3615_ = l_Lean_isLetterLike(v_curr_3598_);
if (v___x_3615_ == 0)
{
uint32_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3616_ = 48;
v___x_3617_ = lean_uint32_dec_le(v___x_3616_, v_curr_3598_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; 
lean_dec(v_acc_3585_);
lean_dec_ref(v_ss_3584_);
v___x_3618_ = lean_box(0);
return v___x_3618_;
}
else
{
uint32_t v___x_3619_; uint8_t v___x_3620_; 
v___x_3619_ = 57;
v___x_3620_ = lean_uint32_dec_le(v_curr_3598_, v___x_3619_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; 
lean_dec(v_acc_3585_);
lean_dec_ref(v_ss_3584_);
v___x_3621_ = lean_box(0);
return v___x_3621_;
}
else
{
lean_object* v___f_3622_; lean_object* v_idPart_3623_; lean_object* v_startPos_3624_; lean_object* v_stopPos_3625_; lean_object* v_startPos_3626_; lean_object* v_stopPos_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___f_3622_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1, &l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
lean_inc_ref(v_ss_3584_);
v_idPart_3623_ = lean_substring_takewhile(v_ss_3584_, v___f_3622_);
v_startPos_3624_ = lean_ctor_get(v_idPart_3623_, 1);
lean_inc(v_startPos_3624_);
v_stopPos_3625_ = lean_ctor_get(v_idPart_3623_, 2);
lean_inc(v_stopPos_3625_);
v_startPos_3626_ = lean_ctor_get(v_ss_3584_, 1);
v_stopPos_3627_ = lean_ctor_get(v_ss_3584_, 2);
v___x_3628_ = lean_nat_sub(v_stopPos_3625_, v_startPos_3624_);
lean_dec(v_startPos_3624_);
lean_dec(v_stopPos_3625_);
v___x_3629_ = lean_nat_sub(v_stopPos_3627_, v_startPos_3626_);
v___x_3630_ = lean_substring_extract(v_ss_3584_, v___x_3628_, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_idPart_3623_);
lean_ctor_set(v___x_3631_, 1, v_acc_3585_);
v_ss_3587_ = v___x_3630_;
v_acc_3588_ = v___x_3631_;
goto v___jp_3586_;
}
}
}
else
{
goto v___jp_3602_;
}
}
else
{
goto v___jp_3602_;
}
}
v___jp_3632_:
{
if (v___y_3633_ == 0)
{
uint32_t v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = 97;
v___x_3635_ = lean_uint32_dec_le(v___x_3634_, v_curr_3598_);
if (v___x_3635_ == 0)
{
goto v___jp_3612_;
}
else
{
uint32_t v___x_3636_; uint8_t v___x_3637_; 
v___x_3636_ = 122;
v___x_3637_ = lean_uint32_dec_le(v_curr_3598_, v___x_3636_);
if (v___x_3637_ == 0)
{
goto v___jp_3612_;
}
else
{
goto v___jp_3602_;
}
}
}
else
{
goto v___jp_3602_;
}
}
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___f_3644_; lean_object* v_escapedPart_3645_; lean_object* v_str_3646_; lean_object* v_startPos_3647_; lean_object* v_stopPos_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3669_; 
v___x_3642_ = lean_box(v___x_3600_);
v___x_3643_ = lean_box(v___x_3597_);
v___f_3644_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3644_, 0, v___x_3642_);
lean_closure_set(v___f_3644_, 1, v___x_3643_);
lean_inc_ref(v_ss_3584_);
v_escapedPart_3645_ = lean_substring_takewhile(v_ss_3584_, v___f_3644_);
v_str_3646_ = lean_ctor_get(v_escapedPart_3645_, 0);
v_startPos_3647_ = lean_ctor_get(v_escapedPart_3645_, 1);
v_stopPos_3648_ = lean_ctor_get(v_escapedPart_3645_, 2);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_escapedPart_3645_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3650_ = v_escapedPart_3645_;
v_isShared_3651_ = v_isSharedCheck_3669_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_stopPos_3648_);
lean_inc(v_startPos_3647_);
lean_inc(v_str_3646_);
lean_dec(v_escapedPart_3645_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3669_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_startPos_3652_; lean_object* v_stopPos_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v_escapedPart_3657_; 
v_startPos_3652_ = lean_ctor_get(v_ss_3584_, 1);
v_stopPos_3653_ = lean_ctor_get(v_ss_3584_, 2);
v___x_3654_ = lean_string_utf8_next(v_str_3646_, v_stopPos_3648_);
lean_dec(v_stopPos_3648_);
lean_inc(v_stopPos_3653_);
v___x_3655_ = lean_string_pos_min(v_stopPos_3653_, v___x_3654_);
lean_inc(v___x_3655_);
lean_inc(v_startPos_3647_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 2, v___x_3655_);
v_escapedPart_3657_ = v___x_3650_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_str_3646_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_startPos_3647_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v___x_3655_);
v_escapedPart_3657_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; uint32_t v___x_3660_; uint32_t v___x_3661_; uint8_t v___x_3662_; 
v___x_3658_ = lean_nat_sub(v___x_3655_, v_startPos_3647_);
lean_dec(v_startPos_3647_);
lean_dec(v___x_3655_);
lean_inc(v___x_3658_);
lean_inc_ref_n(v_escapedPart_3657_, 2);
v___x_3659_ = lean_substring_prev(v_escapedPart_3657_, v___x_3658_);
v___x_3660_ = lean_substring_get(v_escapedPart_3657_, v___x_3659_);
v___x_3661_ = 187;
v___x_3662_ = lean_uint32_dec_eq(v___x_3660_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; 
lean_dec(v___x_3658_);
lean_dec_ref(v_escapedPart_3657_);
lean_dec(v_acc_3585_);
lean_dec_ref(v_ss_3584_);
v___x_3663_ = lean_box(0);
return v___x_3663_;
}
else
{
if (v___x_3597_ == 0)
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_nat_sub(v_stopPos_3653_, v_startPos_3652_);
v___x_3665_ = lean_substring_extract(v_ss_3584_, v___x_3658_, v___x_3664_);
v___x_3666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3666_, 0, v_escapedPart_3657_);
lean_ctor_set(v___x_3666_, 1, v_acc_3585_);
v_ss_3587_ = v___x_3665_;
v_acc_3588_ = v___x_3666_;
goto v___jp_3586_;
}
else
{
lean_object* v___x_3667_; 
lean_dec(v___x_3658_);
lean_dec_ref(v_escapedPart_3657_);
lean_dec(v_acc_3585_);
lean_dec_ref(v_ss_3584_);
v___x_3667_ = lean_box(0);
return v___x_3667_;
}
}
}
}
}
}
else
{
lean_object* v___x_3670_; 
lean_dec(v_acc_3585_);
lean_dec_ref(v_ss_3584_);
v___x_3670_ = lean_box(0);
return v___x_3670_;
}
v___jp_3586_:
{
uint32_t v___x_3589_; uint32_t v___x_3590_; uint8_t v___x_3591_; 
lean_inc_ref(v_ss_3587_);
v___x_3589_ = lean_substring_front(v_ss_3587_);
v___x_3590_ = 46;
v___x_3591_ = lean_uint32_dec_eq(v___x_3589_, v___x_3590_);
if (v___x_3591_ == 0)
{
uint8_t v___x_3592_; 
v___x_3592_ = lean_substring_isempty(v_ss_3587_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; 
lean_dec(v_acc_3588_);
v___x_3593_ = lean_box(0);
return v___x_3593_;
}
else
{
return v_acc_3588_;
}
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = lean_unsigned_to_nat(1u);
v___x_3595_ = lean_substring_drop(v_ss_3587_, v___x_3594_);
v_ss_3584_ = v___x_3595_;
v_acc_3585_ = v_acc_3588_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* v_ss_3671_){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = lean_box(0);
v___x_3673_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_ss_3671_, v___x_3672_);
v___x_3674_ = l_List_reverse___redArg(v___x_3673_);
return v___x_3674_;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3678_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2));
v___x_3679_ = lean_unsigned_to_nat(10u);
v___x_3680_ = lean_unsigned_to_nat(1237u);
v___x_3681_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1));
v___x_3682_ = ((lean_object*)(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0));
v___x_3683_ = l_mkPanicMessageWithDecl(v___x_3682_, v___x_3681_, v___x_3680_, v___x_3679_, v___x_3678_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* v_init_3684_, lean_object* v_x_3685_){
_start:
{
if (lean_obj_tag(v_x_3685_) == 0)
{
lean_inc(v_init_3684_);
return v_init_3684_;
}
else
{
lean_object* v_head_3686_; lean_object* v_tail_3687_; lean_object* v___x_3688_; lean_object* v_comp_3689_; uint32_t v___x_3690_; uint32_t v___x_3691_; uint8_t v___x_3692_; 
v_head_3686_ = lean_ctor_get(v_x_3685_, 0);
lean_inc(v_head_3686_);
v_tail_3687_ = lean_ctor_get(v_x_3685_, 1);
lean_inc(v_tail_3687_);
lean_dec_ref_known(v_x_3685_, 2);
v___x_3688_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3684_, v_tail_3687_);
v_comp_3689_ = lean_substring_tostring(v_head_3686_);
lean_inc_ref(v_comp_3689_);
v___x_3690_ = lean_string_front(v_comp_3689_);
v___x_3691_ = 171;
v___x_3692_ = lean_uint32_dec_eq(v___x_3690_, v___x_3691_);
if (v___x_3692_ == 0)
{
uint32_t v___x_3693_; uint8_t v___x_3694_; 
v___x_3693_ = 48;
v___x_3694_ = lean_uint32_dec_le(v___x_3693_, v___x_3690_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Name_str___override(v___x_3688_, v_comp_3689_);
return v___x_3695_;
}
else
{
uint32_t v___x_3696_; uint8_t v___x_3697_; 
v___x_3696_ = 57;
v___x_3697_ = lean_uint32_dec_le(v___x_3690_, v___x_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_Name_str___override(v___x_3688_, v_comp_3689_);
return v___x_3698_;
}
else
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_comp_3689_);
lean_dec_ref(v_comp_3689_);
if (lean_obj_tag(v___x_3699_) == 1)
{
lean_object* v_val_3700_; lean_object* v___x_3701_; 
v_val_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_val_3700_);
lean_dec_ref_known(v___x_3699_, 1);
v___x_3701_ = l_Lean_Name_num___override(v___x_3688_, v_val_3700_);
return v___x_3701_;
}
else
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec(v___x_3699_);
lean_dec(v___x_3688_);
v___x_3702_ = lean_obj_once(&l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3, &l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3_once, _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
v___x_3703_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_3702_);
return v___x_3703_;
}
}
}
}
else
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3704_ = lean_unsigned_to_nat(1u);
v___x_3705_ = lean_string_drop(v_comp_3689_, v___x_3704_);
v___x_3706_ = lean_string_dropright(v___x_3705_, v___x_3704_);
v___x_3707_ = l_Lean_Name_str___override(v___x_3688_, v___x_3706_);
return v___x_3707_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* v_init_3708_, lean_object* v_x_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v_init_3708_, v_x_3709_);
lean_dec(v_init_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* v_s_3711_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_box(0);
v___x_3713_ = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(v_s_3711_, v___x_3712_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_box(0);
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = lean_box(0);
v___x_3716_ = l_List_foldr___at___00Substring_Raw_toName_spec__0(v___x_3715_, v___x_3713_);
return v___x_3716_;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* v_s_3717_){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3718_ = lean_unsigned_to_nat(0u);
v___x_3719_ = lean_string_utf8_byte_size(v_s_3717_);
v___x_3720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3720_, 0, v_s_3717_);
lean_ctor_set(v___x_3720_, 1, v___x_3718_);
lean_ctor_set(v___x_3720_, 2, v___x_3719_);
v___x_3721_ = l_Substring_Raw_toName(v___x_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* v_s_3722_){
_start:
{
lean_object* v___x_3723_; uint32_t v___x_3724_; uint32_t v___x_3725_; uint8_t v___x_3726_; 
v___x_3723_ = lean_unsigned_to_nat(0u);
v___x_3724_ = lean_string_utf8_get(v_s_3722_, v___x_3723_);
v___x_3725_ = 96;
v___x_3726_ = lean_uint32_dec_eq(v___x_3724_, v___x_3725_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; 
lean_dec_ref(v_s_3722_);
v___x_3727_ = lean_box(0);
return v___x_3727_;
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3728_ = lean_string_utf8_byte_size(v_s_3722_);
v___x_3729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3729_, 0, v_s_3722_);
lean_ctor_set(v___x_3729_, 1, v___x_3723_);
lean_ctor_set(v___x_3729_, 2, v___x_3728_);
v___x_3730_ = lean_unsigned_to_nat(1u);
v___x_3731_ = lean_substring_drop(v___x_3729_, v___x_3730_);
v___x_3732_ = l_Substring_Raw_toName(v___x_3731_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_box(0);
return v___x_3733_;
}
else
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
return v___x_3734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* v_stx_3735_){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l_Lean_Syntax_mkNameLit___closed__1));
v___x_3737_ = l_Lean_Syntax_isLit_x3f(v___x_3736_, v_stx_3735_);
if (lean_obj_tag(v___x_3737_) == 1)
{
lean_object* v_val_3738_; lean_object* v___x_3739_; 
v_val_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_val_3738_);
lean_dec_ref_known(v___x_3737_, 1);
v___x_3739_ = l_Lean_Syntax_decodeNameLit(v_val_3738_);
return v___x_3739_;
}
else
{
lean_object* v___x_3740_; 
lean_dec(v___x_3737_);
v___x_3740_ = lean_box(0);
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* v_stx_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Syntax_isNameLit_x3f(v_stx_3741_);
lean_dec(v_stx_3741_);
return v_res_3742_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* v_x_3743_){
_start:
{
if (lean_obj_tag(v_x_3743_) == 1)
{
lean_object* v_args_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v_args_3744_ = lean_ctor_get(v_x_3743_, 2);
v___x_3745_ = lean_unsigned_to_nat(0u);
v___x_3746_ = lean_array_get_size(v_args_3744_);
v___x_3747_ = lean_nat_dec_lt(v___x_3745_, v___x_3746_);
return v___x_3747_;
}
else
{
uint8_t v___x_3748_; 
v___x_3748_ = 0;
return v___x_3748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* v_x_3749_){
_start:
{
uint8_t v_res_3750_; lean_object* v_r_3751_; 
v_res_3750_ = l_Lean_Syntax_hasArgs(v_x_3749_);
lean_dec(v_x_3749_);
v_r_3751_ = lean_box(v_res_3750_);
return v_r_3751_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* v_x_3752_){
_start:
{
if (lean_obj_tag(v_x_3752_) == 2)
{
uint8_t v___x_3753_; 
v___x_3753_ = 1;
return v___x_3753_;
}
else
{
uint8_t v___x_3754_; 
v___x_3754_ = 0;
return v___x_3754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* v_x_3755_){
_start:
{
uint8_t v_res_3756_; lean_object* v_r_3757_; 
v_res_3756_ = l_Lean_Syntax_isAtom(v_x_3755_);
lean_dec(v_x_3755_);
v_r_3757_ = lean_box(v_res_3756_);
return v_r_3757_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* v_token_3758_, lean_object* v_x_3759_){
_start:
{
if (lean_obj_tag(v_x_3759_) == 2)
{
lean_object* v_val_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v_val_3760_ = lean_ctor_get(v_x_3759_, 1);
lean_inc_ref(v_val_3760_);
lean_dec_ref_known(v_x_3759_, 2);
v___x_3761_ = lean_string_trim(v_val_3760_);
v___x_3762_ = lean_string_trim(v_token_3758_);
v___x_3763_ = lean_string_dec_eq(v___x_3761_, v___x_3762_);
lean_dec_ref(v___x_3762_);
lean_dec_ref(v___x_3761_);
return v___x_3763_;
}
else
{
uint8_t v___x_3764_; 
lean_dec(v_x_3759_);
lean_dec_ref(v_token_3758_);
v___x_3764_ = 0;
return v___x_3764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* v_token_3765_, lean_object* v_x_3766_){
_start:
{
uint8_t v_res_3767_; lean_object* v_r_3768_; 
v_res_3767_ = l_Lean_Syntax_isToken(v_token_3765_, v_x_3766_);
v_r_3768_ = lean_box(v_res_3767_);
return v_r_3768_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* v_stx_3769_){
_start:
{
switch(lean_obj_tag(v_stx_3769_))
{
case 1:
{
lean_object* v_kind_3770_; lean_object* v_args_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v_kind_3770_ = lean_ctor_get(v_stx_3769_, 1);
v_args_3771_ = lean_ctor_get(v_stx_3769_, 2);
v___x_3772_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_3773_ = lean_name_eq(v_kind_3770_, v___x_3772_);
if (v___x_3773_ == 0)
{
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v___x_3774_ = lean_array_get_size(v_args_3771_);
v___x_3775_ = lean_unsigned_to_nat(0u);
v___x_3776_ = lean_nat_dec_eq(v___x_3774_, v___x_3775_);
return v___x_3776_;
}
}
case 0:
{
uint8_t v___x_3777_; 
v___x_3777_ = 1;
return v___x_3777_;
}
default: 
{
uint8_t v___x_3778_; 
v___x_3778_ = 0;
return v___x_3778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* v_stx_3779_){
_start:
{
uint8_t v_res_3780_; lean_object* v_r_3781_; 
v_res_3780_ = l_Lean_Syntax_isNone(v_stx_3779_);
lean_dec(v_stx_3779_);
v_r_3781_ = lean_box(v_res_3780_);
return v_r_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* v_stx_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_Syntax_getOptional_x3f(v_stx_3782_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_box(0);
return v___x_3784_;
}
else
{
lean_object* v_val_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3793_; 
v_val_3785_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3787_ = v___x_3783_;
v_isShared_3788_ = v_isSharedCheck_3793_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_val_3785_);
lean_dec(v___x_3783_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3793_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3789_ = l_Lean_Syntax_getId(v_val_3785_);
lean_dec(v_val_3785_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3789_);
v___x_3791_ = v___x_3787_;
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
return v___x_3791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* v_stx_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_Syntax_getOptionalIdent_x3f(v_stx_3794_);
lean_dec(v_stx_3794_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* v_p_3796_, lean_object* v_x_3797_){
_start:
{
if (lean_obj_tag(v_x_3797_) == 1)
{
lean_object* v_args_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
v_args_3798_ = lean_ctor_get(v_x_3797_, 2);
lean_inc_ref(v_p_3796_);
lean_inc_ref(v_x_3797_);
v___x_3799_ = lean_apply_1(v_p_3796_, v_x_3797_);
v___x_3800_ = lean_unbox(v___x_3799_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; size_t v_sz_3803_; size_t v___x_3804_; lean_object* v___x_3805_; lean_object* v_fst_3806_; 
lean_inc_ref(v_args_3798_);
lean_dec_ref_known(v_x_3797_, 3);
v___x_3801_ = lean_box(0);
v___x_3802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v_sz_3803_ = lean_array_size(v_args_3798_);
v___x_3804_ = ((size_t)0ULL);
v___x_3805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3796_, v_args_3798_, v_sz_3803_, v___x_3804_, v___x_3802_);
lean_dec_ref(v_args_3798_);
v_fst_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_fst_3806_);
lean_dec_ref(v___x_3805_);
if (lean_obj_tag(v_fst_3806_) == 0)
{
return v___x_3801_;
}
else
{
lean_object* v_val_3807_; 
v_val_3807_ = lean_ctor_get(v_fst_3806_, 0);
lean_inc(v_val_3807_);
lean_dec_ref_known(v_fst_3806_, 1);
return v_val_3807_;
}
}
else
{
lean_object* v___x_3808_; 
lean_dec_ref(v_p_3796_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_x_3797_);
return v___x_3808_;
}
}
else
{
lean_object* v___x_3809_; uint8_t v___x_3810_; 
lean_inc(v_x_3797_);
v___x_3809_ = lean_apply_1(v_p_3796_, v_x_3797_);
v___x_3810_ = lean_unbox(v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
lean_dec(v_x_3797_);
v___x_3811_ = lean_box(0);
return v___x_3811_;
}
else
{
lean_object* v___x_3812_; 
v___x_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3812_, 0, v_x_3797_);
return v___x_3812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* v_p_3813_, lean_object* v_as_3814_, size_t v_sz_3815_, size_t v_i_3816_, lean_object* v_b_3817_){
_start:
{
uint8_t v___x_3818_; 
v___x_3818_ = lean_usize_dec_lt(v_i_3816_, v_sz_3815_);
if (v___x_3818_ == 0)
{
lean_dec_ref(v_p_3813_);
lean_inc_ref(v_b_3817_);
return v_b_3817_;
}
else
{
lean_object* v___x_3819_; lean_object* v_a_3820_; lean_object* v___x_3821_; 
v___x_3819_ = lean_box(0);
v_a_3820_ = lean_array_uget_borrowed(v_as_3814_, v_i_3816_);
lean_inc(v_a_3820_);
lean_inc_ref(v_p_3813_);
v___x_3821_ = l_Lean_Syntax_findAux(v_p_3813_, v_a_3820_);
if (lean_obj_tag(v___x_3821_) == 1)
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
lean_dec_ref(v_p_3813_);
v___x_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
v___x_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
lean_ctor_set(v___x_3823_, 1, v___x_3819_);
return v___x_3823_;
}
else
{
lean_object* v___x_3824_; size_t v___x_3825_; size_t v___x_3826_; 
lean_dec(v___x_3821_);
v___x_3824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___closed__0));
v___x_3825_ = ((size_t)1ULL);
v___x_3826_ = lean_usize_add(v_i_3816_, v___x_3825_);
v_i_3816_ = v___x_3826_;
v_b_3817_ = v___x_3824_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* v_p_3828_, lean_object* v_as_3829_, lean_object* v_sz_3830_, lean_object* v_i_3831_, lean_object* v_b_3832_){
_start:
{
size_t v_sz_boxed_3833_; size_t v_i_boxed_3834_; lean_object* v_res_3835_; 
v_sz_boxed_3833_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(v_p_3828_, v_as_3829_, v_sz_boxed_3833_, v_i_boxed_3834_, v_b_3832_);
lean_dec_ref(v_b_3832_);
lean_dec_ref(v_as_3829_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* v_stx_3836_, lean_object* v_p_3837_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_Syntax_findAux(v_p_3837_, v_stx_3836_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* v_s_3839_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_Syntax_isNatLit_x3f(v_s_3839_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_unsigned_to_nat(0u);
return v___x_3841_;
}
else
{
lean_object* v_val_3842_; 
v_val_3842_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_val_3842_);
lean_dec_ref_known(v___x_3840_, 1);
return v_val_3842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* v_s_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_TSyntax_getNat(v_s_3843_);
lean_dec(v_s_3843_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* v_stx_3848_){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3850_ = l_Lean_Syntax_isLit_x3f(v___x_3849_, v_stx_3848_);
if (lean_obj_tag(v___x_3850_) == 1)
{
lean_object* v_val_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_val_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_val_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3852_ = lean_unsigned_to_nat(0u);
v___x_3853_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(v_val_3851_, v___x_3852_, v___x_3852_);
lean_dec(v_val_3851_);
return v___x_3853_;
}
else
{
lean_object* v___x_3854_; 
lean_dec(v___x_3850_);
v___x_3854_ = lean_box(0);
return v___x_3854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* v_stx_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_stx_3855_);
lean_dec(v_stx_3855_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* v_s_3857_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(v_s_3857_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_unsigned_to_nat(0u);
return v___x_3859_;
}
else
{
lean_object* v_val_3860_; 
v_val_3860_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v___x_3858_, 1);
return v_val_3860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* v_s_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_TSyntax_getHexNumVal(v_s_3861_);
lean_dec(v_s_3861_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* v_s_3863_, lean_object* v_p_3864_, lean_object* v_n_3865_){
_start:
{
uint8_t v___x_3866_; 
v___x_3866_ = lean_string_utf8_at_end(v_s_3863_, v_p_3864_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; uint32_t v___x_3868_; uint32_t v___x_3869_; uint8_t v___x_3870_; 
v___x_3867_ = lean_string_utf8_next(v_s_3863_, v_p_3864_);
v___x_3868_ = lean_string_utf8_get(v_s_3863_, v_p_3864_);
lean_dec(v_p_3864_);
v___x_3869_ = 95;
v___x_3870_ = lean_uint32_dec_eq(v___x_3868_, v___x_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = lean_unsigned_to_nat(1u);
v___x_3872_ = lean_nat_add(v_n_3865_, v___x_3871_);
lean_dec(v_n_3865_);
v_p_3864_ = v___x_3867_;
v_n_3865_ = v___x_3872_;
goto _start;
}
else
{
v_p_3864_ = v___x_3867_;
goto _start;
}
}
else
{
lean_dec(v_p_3864_);
return v_n_3865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* v_s_3875_, lean_object* v_p_3876_, lean_object* v_n_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_s_3875_, v_p_3876_, v_n_3877_);
lean_dec_ref(v_s_3875_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* v_s_3879_){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1));
v___x_3881_ = l_Lean_Syntax_isLit_x3f(v___x_3880_, v_s_3879_);
if (lean_obj_tag(v___x_3881_) == 1)
{
lean_object* v_val_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_val_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_val_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(v_val_3882_, v___x_3883_, v___x_3883_);
lean_dec(v_val_3882_);
return v___x_3884_;
}
else
{
lean_object* v___x_3885_; 
lean_dec(v___x_3881_);
v___x_3885_ = lean_unsigned_to_nat(0u);
return v___x_3885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* v_s_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_TSyntax_getHexNumSize(v_s_3886_);
lean_dec(v_s_3886_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* v_s_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_Syntax_getId(v_s_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* v_s_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Lean_TSyntax_getId(v_s_3890_);
lean_dec(v_s_3890_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* v_s_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Syntax_isScientificLit_x3f(v_s_3899_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v___x_3901_; 
v___x_3901_ = ((lean_object*)(l_Lean_TSyntax_getScientific___closed__1));
return v___x_3901_;
}
else
{
lean_object* v_val_3902_; 
v_val_3902_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_val_3902_);
lean_dec_ref_known(v___x_3900_, 1);
return v_val_3902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* v_s_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_TSyntax_getScientific(v_s_3903_);
lean_dec(v_s_3903_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* v_s_3905_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_Syntax_isStrLit_x3f(v_s_3905_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v___x_3907_; 
v___x_3907_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_3907_;
}
else
{
lean_object* v_val_3908_; 
v_val_3908_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_val_3908_);
lean_dec_ref_known(v___x_3906_, 1);
return v_val_3908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* v_s_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_TSyntax_getString(v_s_3909_);
lean_dec(v_s_3909_);
return v_res_3910_;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* v_s_3911_){
_start:
{
lean_object* v___x_3912_; 
v___x_3912_ = l_Lean_Syntax_isCharLit_x3f(v_s_3911_);
if (lean_obj_tag(v___x_3912_) == 0)
{
uint32_t v___x_3913_; 
v___x_3913_ = 65;
return v___x_3913_;
}
else
{
lean_object* v_val_3914_; uint32_t v___x_3915_; 
v_val_3914_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_val_3914_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3915_ = lean_unbox_uint32(v_val_3914_);
lean_dec(v_val_3914_);
return v___x_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* v_s_3916_){
_start:
{
uint32_t v_res_3917_; lean_object* v_r_3918_; 
v_res_3917_ = l_Lean_TSyntax_getChar(v_s_3916_);
lean_dec(v_s_3916_);
v_r_3918_ = lean_box_uint32(v_res_3917_);
return v_r_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* v_s_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_Syntax_isNameLit_x3f(v_s_3919_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v___x_3921_; 
v___x_3921_ = lean_box(0);
return v___x_3921_;
}
else
{
lean_object* v_val_3922_; 
v_val_3922_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_val_3922_);
lean_dec_ref_known(v___x_3920_, 1);
return v_val_3922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* v_s_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lean_TSyntax_getName(v_s_3923_);
lean_dec(v_s_3923_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* v_s_3925_){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = l_Lean_Syntax_getArg(v_s_3925_, v___x_3926_);
v___x_3928_ = l_Lean_Syntax_getId(v___x_3927_);
lean_dec(v___x_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* v_s_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_TSyntax_getHygieneInfo(v_s_3929_);
lean_dec(v_s_3929_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* v_sep_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_Syntax_SepArray_ofElems(v_sep_3931_, v_a_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* v_sep_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(v_sep_3934_, v_a_3935_);
lean_dec_ref(v_a_3935_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* v_sep_3937_){
_start:
{
lean_object* v___f_3938_; 
v___f_3938_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3938_, 0, v_sep_3937_);
return v___f_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* v_k_3939_, lean_object* v_sep_3940_){
_start:
{
lean_object* v___f_3941_; 
v___f_3941_ = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3941_, 0, v_sep_3940_);
return v___f_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* v_k_3942_, lean_object* v_sep_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(v_k_3942_, v_sep_3943_);
lean_dec(v_k_3942_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* v_s_3945_, lean_object* v_val_3946_, uint8_t v_canonical_3947_){
_start:
{
lean_object* v___x_3948_; lean_object* v_src_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v_imported_3952_; lean_object* v_ctx_3953_; lean_object* v_scopes_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3970_; 
v___x_3948_ = lean_unsigned_to_nat(0u);
v_src_3949_ = l_Lean_Syntax_getArg(v_s_3945_, v___x_3948_);
v___x_3950_ = l_Lean_Syntax_getId(v_src_3949_);
v___x_3951_ = l_Lean_extractMacroScopes(v___x_3950_);
v_imported_3952_ = lean_ctor_get(v___x_3951_, 1);
v_ctx_3953_ = lean_ctor_get(v___x_3951_, 2);
v_scopes_3954_ = lean_ctor_get(v___x_3951_, 3);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3970_ == 0)
{
lean_object* v_unused_3971_; 
v_unused_3971_ = lean_ctor_get(v___x_3951_, 0);
lean_dec(v_unused_3971_);
v___x_3956_ = v___x_3951_;
v_isShared_3957_ = v_isSharedCheck_3970_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_scopes_3954_);
lean_inc(v_ctx_3953_);
lean_inc(v_imported_3952_);
lean_dec(v___x_3951_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3970_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3958_ = l_Lean_Name_eraseMacroScopes(v_val_3946_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v___x_3958_);
v___x_3960_ = v___x_3956_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3969_, 1, v_imported_3952_);
lean_ctor_set(v_reuseFailAlloc_3969_, 2, v_ctx_3953_);
lean_ctor_set(v_reuseFailAlloc_3969_, 3, v_scopes_3954_);
v___x_3960_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v_id_3961_; lean_object* v___x_3962_; uint8_t v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_id_3961_ = l_Lean_MacroScopesView_review(v___x_3960_);
v___x_3962_ = l_Lean_SourceInfo_fromRef(v_src_3949_, v_canonical_3947_);
lean_dec(v_src_3949_);
v___x_3963_ = 1;
v___x_3964_ = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(v_val_3946_, v___x_3963_);
v___x_3965_ = lean_string_utf8_byte_size(v___x_3964_);
v___x_3966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3964_);
lean_ctor_set(v___x_3966_, 1, v___x_3948_);
lean_ctor_set(v___x_3966_, 2, v___x_3965_);
v___x_3967_ = lean_box(0);
v___x_3968_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3962_);
lean_ctor_set(v___x_3968_, 1, v___x_3966_);
lean_ctor_set(v___x_3968_, 2, v_id_3961_);
lean_ctor_set(v___x_3968_, 3, v___x_3967_);
return v___x_3968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* v_s_3972_, lean_object* v_val_3973_, lean_object* v_canonical_3974_){
_start:
{
uint8_t v_canonical_boxed_3975_; lean_object* v_res_3976_; 
v_canonical_boxed_3975_ = lean_unbox(v_canonical_3974_);
v_res_3976_ = l_Lean_HygieneInfo_mkIdent(v_s_3972_, v_val_3973_, v_canonical_boxed_3975_);
lean_dec(v_s_3972_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* v_inst_3977_, lean_object* v_inst_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = lean_apply_1(v_inst_3977_, v_a_3979_);
v___x_3981_ = lean_apply_1(v_inst_3978_, v___x_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* v_inst_3982_, lean_object* v_inst_3983_){
_start:
{
lean_object* v___f_3984_; 
v___f_3984_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3984_, 0, v_inst_3982_);
lean_closure_set(v___f_3984_, 1, v_inst_3983_);
return v___f_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* v_00_u03b1_3985_, lean_object* v_k_3986_, lean_object* v_k_x27_3987_, lean_object* v_inst_3988_, lean_object* v_inst_3989_){
_start:
{
lean_object* v___f_3990_; 
v___f_3990_ = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3990_, 0, v_inst_3988_);
lean_closure_set(v___f_3990_, 1, v_inst_3989_);
return v___f_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* v_00_u03b1_3991_, lean_object* v_k_3992_, lean_object* v_k_x27_3993_, lean_object* v_inst_3994_, lean_object* v_inst_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(v_00_u03b1_3991_, v_k_3992_, v_k_x27_3993_, v_inst_3994_, v_inst_3995_);
lean_dec(v_k_x27_3993_);
lean_dec(v_k_3992_);
return v_res_3996_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2));
v___x_4005_ = l_Lean_mkCIdent(v___x_4004_);
return v___x_4005_;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = ((lean_object*)(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5));
v___x_4011_ = l_Lean_mkCIdent(v___x_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t v_x_4012_){
_start:
{
if (v_x_4012_ == 0)
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__3, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__3_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
return v___x_4013_;
}
else
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_obj_once(&l_Lean_instQuoteBoolMkStr1___lam__0___closed__6, &l_Lean_instQuoteBoolMkStr1___lam__0___closed__6_once, _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
return v___x_4014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* v_x_4015_){
_start:
{
uint8_t v_x_85__boxed_4016_; lean_object* v_res_4017_; 
v_x_85__boxed_4016_ = lean_unbox(v_x_4015_);
v_res_4017_ = l_Lean_instQuoteBoolMkStr1___lam__0(v_x_85__boxed_4016_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t v_val_4020_){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4021_ = lean_box(2);
v___x_4022_ = l_Lean_Syntax_mkCharLit(v_val_4020_, v___x_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* v_val_4023_){
_start:
{
uint32_t v_val_boxed_4024_; lean_object* v_res_4025_; 
v_val_boxed_4024_ = lean_unbox_uint32(v_val_4023_);
lean_dec(v_val_4023_);
v_res_4025_ = l_Lean_instQuoteCharCharLitKind___lam__0(v_val_boxed_4024_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* v_val_4028_){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = lean_box(2);
v___x_4030_ = l_Lean_Syntax_mkStrLit(v_val_4028_, v___x_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* v_n_4033_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4034_ = l_Nat_reprFast(v_n_4033_);
v___x_4035_ = lean_box(2);
v___x_4036_ = l_Lean_Syntax_mkNumLit(v___x_4034_, v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* v_s_4044_){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4045_ = ((lean_object*)(l_Lean_instQuoteRawMkStr1___lam__0___closed__2));
v___x_4046_ = lean_substring_tostring(v_s_4044_);
v___x_4047_ = lean_box(2);
v___x_4048_ = l_Lean_Syntax_mkStrLit(v___x_4046_, v___x_4047_);
v___x_4049_ = lean_unsigned_to_nat(1u);
v___x_4050_ = lean_mk_empty_array_with_capacity(v___x_4049_);
v___x_4051_ = lean_array_push(v___x_4050_, v___x_4048_);
v___x_4052_ = l_Lean_Syntax_mkCApp(v___x_4045_, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* v_acc_4055_, lean_object* v_x_4056_){
_start:
{
switch(lean_obj_tag(v_x_4056_))
{
case 0:
{
uint8_t v___x_4057_; 
v___x_4057_ = l_List_isEmpty___redArg(v_acc_4055_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4058_, 0, v_acc_4055_);
return v___x_4058_;
}
else
{
lean_object* v___x_4059_; 
lean_dec(v_acc_4055_);
v___x_4059_ = lean_box(0);
return v___x_4059_;
}
}
case 1:
{
lean_object* v_pre_4060_; lean_object* v_str_4061_; lean_object* v_val_4063_; lean_object* v___x_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v_pre_4060_ = lean_ctor_get(v_x_4056_, 0);
lean_inc(v_pre_4060_);
v_str_4061_ = lean_ctor_get(v_x_4056_, 1);
lean_inc_ref(v_str_4061_);
lean_dec_ref_known(v_x_4056_, 2);
v___x_4066_ = lean_unsigned_to_nat(0u);
v___x_4067_ = lean_string_utf8_byte_size(v_str_4061_);
v___x_4068_ = lean_nat_dec_lt(v___x_4066_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4069_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4070_ = lean_string_append(v___x_4069_, v_str_4061_);
lean_dec_ref(v_str_4061_);
v___x_4071_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4072_ = lean_string_append(v___x_4070_, v___x_4071_);
v_val_4063_ = v___x_4072_;
goto v___jp_4062_;
}
else
{
lean_object* v___f_4073_; uint8_t v___y_4075_; lean_object* v___f_4082_; uint32_t v___y_4089_; uint32_t v___y_4094_; uint8_t v___y_4095_; uint8_t v_c_4109_; uint8_t v___x_4118_; uint8_t v___x_4119_; 
v___f_4073_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0));
v___f_4082_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1));
v_c_4109_ = lean_string_get_byte_fast(v_str_4061_, v___x_4066_);
v___x_4118_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2);
v___x_4119_ = lean_uint8_dec_le(v___x_4118_, v_c_4109_);
if (v___x_4119_ == 0)
{
goto v___jp_4113_;
}
else
{
uint8_t v___x_4120_; uint8_t v___x_4121_; 
v___x_4120_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3);
v___x_4121_ = lean_uint8_dec_le(v_c_4109_, v___x_4120_);
if (v___x_4121_ == 0)
{
goto v___jp_4113_;
}
else
{
goto v___jp_4106_;
}
}
v___jp_4074_:
{
if (v___y_4075_ == 0)
{
uint8_t v___x_4076_; 
lean_inc_ref(v_str_4061_);
v___x_4076_ = lean_string_any(v_str_4061_, v___f_4073_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4077_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
v___x_4078_ = lean_string_append(v___x_4077_, v_str_4061_);
lean_dec_ref(v_str_4061_);
v___x_4079_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1, &l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
v___x_4080_ = lean_string_append(v___x_4078_, v___x_4079_);
v_val_4063_ = v___x_4080_;
goto v___jp_4062_;
}
else
{
lean_object* v___x_4081_; 
lean_dec_ref(v_str_4061_);
lean_dec(v_pre_4060_);
lean_dec(v_acc_4055_);
v___x_4081_ = lean_box(0);
return v___x_4081_;
}
}
else
{
v_val_4063_ = v_str_4061_;
goto v___jp_4062_;
}
}
v___jp_4083_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; uint8_t v___x_4087_; 
lean_inc_ref(v_str_4061_);
v___x_4084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4084_, 0, v_str_4061_);
lean_ctor_set(v___x_4084_, 1, v___x_4066_);
lean_ctor_set(v___x_4084_, 2, v___x_4067_);
v___x_4085_ = lean_unsigned_to_nat(1u);
v___x_4086_ = lean_substring_drop(v___x_4084_, v___x_4085_);
v___x_4087_ = lean_substring_all(v___x_4086_, v___f_4082_);
v___y_4075_ = v___x_4087_;
goto v___jp_4074_;
}
v___jp_4088_:
{
uint32_t v___x_4090_; uint8_t v___x_4091_; 
v___x_4090_ = 95;
v___x_4091_ = lean_uint32_dec_eq(v___y_4089_, v___x_4090_);
if (v___x_4091_ == 0)
{
uint8_t v___x_4092_; 
v___x_4092_ = l_Lean_isLetterLike(v___y_4089_);
if (v___x_4092_ == 0)
{
v___y_4075_ = v___x_4092_;
goto v___jp_4074_;
}
else
{
goto v___jp_4083_;
}
}
else
{
goto v___jp_4083_;
}
}
v___jp_4093_:
{
if (v___y_4095_ == 0)
{
uint32_t v___x_4096_; uint8_t v___x_4097_; 
v___x_4096_ = 97;
v___x_4097_ = lean_uint32_dec_le(v___x_4096_, v___y_4094_);
if (v___x_4097_ == 0)
{
v___y_4089_ = v___y_4094_;
goto v___jp_4088_;
}
else
{
uint32_t v___x_4098_; uint8_t v___x_4099_; 
v___x_4098_ = 122;
v___x_4099_ = lean_uint32_dec_le(v___y_4094_, v___x_4098_);
if (v___x_4099_ == 0)
{
v___y_4089_ = v___y_4094_;
goto v___jp_4088_;
}
else
{
goto v___jp_4083_;
}
}
}
else
{
goto v___jp_4083_;
}
}
v___jp_4100_:
{
uint32_t v___x_4101_; uint32_t v___x_4102_; uint8_t v___x_4103_; 
v___x_4101_ = lean_string_utf8_get(v_str_4061_, v___x_4066_);
v___x_4102_ = 65;
v___x_4103_ = lean_uint32_dec_le(v___x_4102_, v___x_4101_);
if (v___x_4103_ == 0)
{
v___y_4094_ = v___x_4101_;
v___y_4095_ = v___x_4103_;
goto v___jp_4093_;
}
else
{
uint32_t v___x_4104_; uint8_t v___x_4105_; 
v___x_4104_ = 90;
v___x_4105_ = lean_uint32_dec_le(v___x_4101_, v___x_4104_);
v___y_4094_ = v___x_4101_;
v___y_4095_ = v___x_4105_;
goto v___jp_4093_;
}
}
v___jp_4106_:
{
lean_object* v___x_4107_; uint8_t v___x_4108_; 
v___x_4107_ = lean_unsigned_to_nat(1u);
v___x_4108_ = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(v_str_4061_, v___x_4107_);
if (v___x_4108_ == 0)
{
goto v___jp_4100_;
}
else
{
v___y_4075_ = v___x_4108_;
goto v___jp_4074_;
}
}
v___jp_4110_:
{
uint8_t v___x_4111_; uint8_t v___x_4112_; 
v___x_4111_ = lean_uint8_once(&l_Lean_isIdFirstAscii___closed__0, &l_Lean_isIdFirstAscii___closed__0_once, _init_l_Lean_isIdFirstAscii___closed__0);
v___x_4112_ = lean_uint8_dec_eq(v_c_4109_, v___x_4111_);
if (v___x_4112_ == 0)
{
goto v___jp_4100_;
}
else
{
goto v___jp_4106_;
}
}
v___jp_4113_:
{
uint8_t v___x_4114_; uint8_t v___x_4115_; 
v___x_4114_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0);
v___x_4115_ = lean_uint8_dec_le(v___x_4114_, v_c_4109_);
if (v___x_4115_ == 0)
{
goto v___jp_4110_;
}
else
{
uint8_t v___x_4116_; uint8_t v___x_4117_; 
v___x_4116_ = lean_uint8_once(&l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1, &l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1_once, _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1);
v___x_4117_ = lean_uint8_dec_le(v_c_4109_, v___x_4116_);
if (v___x_4117_ == 0)
{
goto v___jp_4110_;
}
else
{
goto v___jp_4106_;
}
}
}
}
v___jp_4062_:
{
lean_object* v___x_4064_; 
v___x_4064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4064_, 0, v_val_4063_);
lean_ctor_set(v___x_4064_, 1, v_acc_4055_);
v_acc_4055_ = v___x_4064_;
v_x_4056_ = v_pre_4060_;
goto _start;
}
}
default: 
{
lean_object* v___x_4122_; 
lean_dec_ref_known(v_x_4056_, 2);
lean_dec(v_acc_4055_);
v___x_4122_ = lean_box(0);
return v___x_4122_;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4129_ = ((lean_object*)(l_Lean_quoteNameMk___closed__2));
v___x_4130_ = l_Lean_mkCIdent(v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* v_x_4141_){
_start:
{
switch(lean_obj_tag(v_x_4141_))
{
case 0:
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_obj_once(&l_Lean_quoteNameMk___closed__3, &l_Lean_quoteNameMk___closed__3_once, _init_l_Lean_quoteNameMk___closed__3);
return v___x_4142_;
}
case 1:
{
lean_object* v_pre_4143_; lean_object* v_str_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v_pre_4143_ = lean_ctor_get(v_x_4141_, 0);
lean_inc(v_pre_4143_);
v_str_4144_ = lean_ctor_get(v_x_4141_, 1);
lean_inc_ref(v_str_4144_);
lean_dec_ref_known(v_x_4141_, 2);
v___x_4145_ = ((lean_object*)(l_Lean_quoteNameMk___closed__5));
v___x_4146_ = l_Lean_quoteNameMk(v_pre_4143_);
v___x_4147_ = lean_box(2);
v___x_4148_ = l_Lean_Syntax_mkStrLit(v_str_4144_, v___x_4147_);
v___x_4149_ = lean_unsigned_to_nat(2u);
v___x_4150_ = lean_mk_empty_array_with_capacity(v___x_4149_);
v___x_4151_ = lean_array_push(v___x_4150_, v___x_4146_);
v___x_4152_ = lean_array_push(v___x_4151_, v___x_4148_);
v___x_4153_ = l_Lean_Syntax_mkCApp(v___x_4145_, v___x_4152_);
return v___x_4153_;
}
default: 
{
lean_object* v_pre_4154_; lean_object* v_i_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_pre_4154_ = lean_ctor_get(v_x_4141_, 0);
lean_inc(v_pre_4154_);
v_i_4155_ = lean_ctor_get(v_x_4141_, 1);
lean_inc(v_i_4155_);
lean_dec_ref_known(v_x_4141_, 2);
v___x_4156_ = ((lean_object*)(l_Lean_quoteNameMk___closed__7));
v___x_4157_ = l_Lean_quoteNameMk(v_pre_4154_);
v___x_4158_ = l_Nat_reprFast(v_i_4155_);
v___x_4159_ = lean_box(2);
v___x_4160_ = l_Lean_Syntax_mkNumLit(v___x_4158_, v___x_4159_);
v___x_4161_ = lean_unsigned_to_nat(2u);
v___x_4162_ = lean_mk_empty_array_with_capacity(v___x_4161_);
v___x_4163_ = lean_array_push(v___x_4162_, v___x_4157_);
v___x_4164_ = lean_array_push(v___x_4163_, v___x_4160_);
v___x_4165_ = l_Lean_Syntax_mkCApp(v___x_4156_, v___x_4164_);
return v___x_4165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* v_n_4172_){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_box(0);
lean_inc(v_n_4172_);
v___x_4174_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4173_, v_n_4172_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_quoteNameMk(v_n_4172_);
return v___x_4175_;
}
else
{
lean_object* v_val_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_dec(v_n_4172_);
v_val_4176_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_val_4176_);
lean_dec_ref_known(v___x_4174_, 1);
v___x_4177_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4178_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4179_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4180_ = lean_string_intercalate(v___x_4179_, v_val_4176_);
v___x_4181_ = lean_string_append(v___x_4178_, v___x_4180_);
lean_dec_ref(v___x_4180_);
v___x_4182_ = lean_box(2);
v___x_4183_ = l_Lean_Syntax_mkNameLit(v___x_4181_, v___x_4182_);
v___x_4184_ = lean_unsigned_to_nat(1u);
v___x_4185_ = lean_mk_empty_array_with_capacity(v___x_4184_);
v___x_4186_ = lean_array_push(v___x_4185_, v___x_4183_);
v___x_4187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4182_);
lean_ctor_set(v___x_4187_, 1, v___x_4177_);
lean_ctor_set(v___x_4187_, 2, v___x_4186_);
return v___x_4187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___lam__0(lean_object* v_n_4188_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_box(0);
lean_inc(v_n_4188_);
v___x_4190_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_4189_, v_n_4188_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_quoteNameMk(v_n_4188_);
return v___x_4191_;
}
else
{
lean_object* v_val_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
lean_dec(v_n_4188_);
v_val_4192_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_val_4192_);
lean_dec_ref_known(v___x_4190_, 1);
v___x_4193_ = ((lean_object*)(l_Lean_instQuoteNameMkStr1___private__1___closed__1));
v___x_4194_ = ((lean_object*)(l_Lean_Name_reprPrec___closed__2));
v___x_4195_ = ((lean_object*)(l_Lean_versionStringCore___closed__1));
v___x_4196_ = lean_string_intercalate(v___x_4195_, v_val_4192_);
v___x_4197_ = lean_string_append(v___x_4194_, v___x_4196_);
lean_dec_ref(v___x_4196_);
v___x_4198_ = lean_box(2);
v___x_4199_ = l_Lean_Syntax_mkNameLit(v___x_4197_, v___x_4198_);
v___x_4200_ = lean_unsigned_to_nat(1u);
v___x_4201_ = lean_mk_empty_array_with_capacity(v___x_4200_);
v___x_4202_ = lean_array_push(v___x_4201_, v___x_4199_);
v___x_4203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4198_);
lean_ctor_set(v___x_4203_, 1, v___x_4193_);
lean_ctor_set(v___x_4203_, 2, v___x_4202_);
return v___x_4203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* v_inst_4211_, lean_object* v_inst_4212_, lean_object* v_x_4213_){
_start:
{
lean_object* v_fst_4214_; lean_object* v_snd_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v_fst_4214_ = lean_ctor_get(v_x_4213_, 0);
lean_inc(v_fst_4214_);
v_snd_4215_ = lean_ctor_get(v_x_4213_, 1);
lean_inc(v_snd_4215_);
lean_dec_ref(v_x_4213_);
v___x_4216_ = ((lean_object*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2));
v___x_4217_ = lean_apply_1(v_inst_4211_, v_fst_4214_);
v___x_4218_ = lean_apply_1(v_inst_4212_, v_snd_4215_);
v___x_4219_ = lean_unsigned_to_nat(2u);
v___x_4220_ = lean_mk_empty_array_with_capacity(v___x_4219_);
v___x_4221_ = lean_array_push(v___x_4220_, v___x_4217_);
v___x_4222_ = lean_array_push(v___x_4221_, v___x_4218_);
v___x_4223_ = l_Lean_Syntax_mkCApp(v___x_4216_, v___x_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* v_inst_4224_, lean_object* v_inst_4225_){
_start:
{
lean_object* v___f_4226_; 
v___f_4226_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4226_, 0, v_inst_4224_);
lean_closure_set(v___f_4226_, 1, v_inst_4225_);
return v___f_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* v_00_u03b1_4227_, lean_object* v_00_u03b2_4228_, lean_object* v_inst_4229_, lean_object* v_inst_4230_){
_start:
{
lean_object* v___f_4231_; 
v___f_4231_ = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4231_, 0, v_inst_4229_);
lean_closure_set(v___f_4231_, 1, v_inst_4230_);
return v___f_4231_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3(void){
_start:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2));
v___x_4238_ = l_Lean_mkCIdent(v___x_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* v_inst_4243_, lean_object* v_x_4244_){
_start:
{
if (lean_obj_tag(v_x_4244_) == 0)
{
lean_object* v___x_4245_; 
lean_dec_ref(v_inst_4243_);
v___x_4245_ = lean_obj_once(&l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3, &l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3_once, _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
return v___x_4245_;
}
else
{
lean_object* v_head_4246_; lean_object* v_tail_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_head_4246_ = lean_ctor_get(v_x_4244_, 0);
lean_inc(v_head_4246_);
v_tail_4247_ = lean_ctor_get(v_x_4244_, 1);
lean_inc(v_tail_4247_);
lean_dec_ref_known(v_x_4244_, 2);
v___x_4248_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5));
lean_inc_ref(v_inst_4243_);
v___x_4249_ = lean_apply_1(v_inst_4243_, v_head_4246_);
v___x_4250_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4243_, v_tail_4247_);
v___x_4251_ = lean_unsigned_to_nat(2u);
v___x_4252_ = lean_mk_empty_array_with_capacity(v___x_4251_);
v___x_4253_ = lean_array_push(v___x_4252_, v___x_4249_);
v___x_4254_ = lean_array_push(v___x_4253_, v___x_4250_);
v___x_4255_ = l_Lean_Syntax_mkCApp(v___x_4248_, v___x_4254_);
return v___x_4255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* v_00_u03b1_4256_, lean_object* v_inst_4257_, lean_object* v_x_4258_){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4257_, v_x_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* v_inst_4260_, lean_object* v_a_4261_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4260_, v_a_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* v_00_u03b1_4263_, lean_object* v_inst_4264_, lean_object* v_a_4265_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4264_, v_a_4265_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* v_inst_4267_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4268_, 0, lean_box(0));
lean_closure_set(v___x_4268_, 1, v_inst_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* v_00_u03b1_4269_, lean_object* v_inst_4270_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4271_, 0, lean_box(0));
lean_closure_set(v___x_4271_, 1, v_inst_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* v_inst_4274_, lean_object* v_xs_4275_, lean_object* v_i_4276_, lean_object* v_args_4277_){
_start:
{
lean_object* v___x_4278_; uint8_t v___x_4279_; 
v___x_4278_ = lean_array_get_size(v_xs_4275_);
v___x_4279_ = lean_nat_dec_lt(v_i_4276_, v___x_4278_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
lean_dec(v_i_4276_);
lean_dec_ref(v_inst_4274_);
v___x_4280_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0));
v___x_4281_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1));
v___x_4282_ = l_Nat_reprFast(v___x_4278_);
v___x_4283_ = lean_string_append(v___x_4281_, v___x_4282_);
lean_dec_ref(v___x_4282_);
v___x_4284_ = l_Lean_Name_mkStr2(v___x_4280_, v___x_4283_);
v___x_4285_ = l_Lean_Syntax_mkCApp(v___x_4284_, v_args_4277_);
return v___x_4285_;
}
else
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4286_ = lean_unsigned_to_nat(1u);
v___x_4287_ = lean_nat_add(v_i_4276_, v___x_4286_);
v___x_4288_ = lean_array_fget_borrowed(v_xs_4275_, v_i_4276_);
lean_dec(v_i_4276_);
lean_inc_ref(v_inst_4274_);
lean_inc(v___x_4288_);
v___x_4289_ = lean_apply_1(v_inst_4274_, v___x_4288_);
v___x_4290_ = lean_array_push(v_args_4277_, v___x_4289_);
v_i_4276_ = v___x_4287_;
v_args_4277_ = v___x_4290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* v_inst_4292_, lean_object* v_xs_4293_, lean_object* v_i_4294_, lean_object* v_args_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4292_, v_xs_4293_, v_i_4294_, v_args_4295_);
lean_dec_ref(v_xs_4293_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* v_00_u03b1_4297_, lean_object* v_inst_4298_, lean_object* v_xs_4299_, lean_object* v_i_4300_, lean_object* v_args_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4298_, v_xs_4299_, v_i_4300_, v_args_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* v_00_u03b1_4303_, lean_object* v_inst_4304_, lean_object* v_xs_4305_, lean_object* v_i_4306_, lean_object* v_args_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(v_00_u03b1_4303_, v_inst_4304_, v_xs_4305_, v_i_4306_, v_args_4307_);
lean_dec_ref(v_xs_4305_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* v_inst_4313_, lean_object* v_xs_4314_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4315_ = lean_array_get_size(v_xs_4314_);
v___x_4316_ = lean_unsigned_to_nat(8u);
v___x_4317_ = lean_nat_dec_le(v___x_4315_, v___x_4316_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4318_ = ((lean_object*)(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1));
v___x_4319_ = lean_array_to_list(v_xs_4314_);
v___x_4320_ = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(v_inst_4313_, v___x_4319_);
v___x_4321_ = lean_unsigned_to_nat(1u);
v___x_4322_ = lean_mk_empty_array_with_capacity(v___x_4321_);
v___x_4323_ = lean_array_push(v___x_4322_, v___x_4320_);
v___x_4324_ = l_Lean_Syntax_mkCApp(v___x_4318_, v___x_4323_);
return v___x_4324_;
}
else
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4327_ = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(v_inst_4313_, v_xs_4314_, v___x_4325_, v___x_4326_);
lean_dec_ref(v_xs_4314_);
return v___x_4327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* v_00_u03b1_4328_, lean_object* v_inst_4329_, lean_object* v_xs_4330_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4329_, v_xs_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* v_inst_4332_, lean_object* v_xs_4333_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4332_, v_xs_4333_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* v_00_u03b1_4335_, lean_object* v_inst_4336_, lean_object* v_xs_4337_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(v_inst_4336_, v_xs_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* v_inst_4339_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4340_, 0, lean_box(0));
lean_closure_set(v___x_4340_, 1, v_inst_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* v_00_u03b1_4341_, lean_object* v_inst_4342_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(v___x_4343_, 0, lean_box(0));
lean_closure_set(v___x_4343_, 1, v_inst_4342_);
return v___x_4343_;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__2));
v___x_4350_ = l_Lean_mkIdent(v___x_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* v_inst_4355_, lean_object* v_x_4356_){
_start:
{
if (lean_obj_tag(v_x_4356_) == 0)
{
lean_object* v___x_4357_; 
lean_dec_ref(v_inst_4355_);
v___x_4357_ = lean_obj_once(&l_Lean_Option_hasQuote___redArg___lam__0___closed__3, &l_Lean_Option_hasQuote___redArg___lam__0___closed__3_once, _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
return v___x_4357_;
}
else
{
lean_object* v_val_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v_val_4358_ = lean_ctor_get(v_x_4356_, 0);
lean_inc(v_val_4358_);
lean_dec_ref_known(v_x_4356_, 1);
v___x_4359_ = ((lean_object*)(l_Lean_Option_hasQuote___redArg___lam__0___closed__5));
v___x_4360_ = lean_apply_1(v_inst_4355_, v_val_4358_);
v___x_4361_ = lean_unsigned_to_nat(1u);
v___x_4362_ = lean_mk_empty_array_with_capacity(v___x_4361_);
v___x_4363_ = lean_array_push(v___x_4362_, v___x_4360_);
v___x_4364_ = l_Lean_Syntax_mkCApp(v___x_4359_, v___x_4363_);
return v___x_4364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* v_inst_4365_){
_start:
{
lean_object* v___f_4366_; 
v___f_4366_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4366_, 0, v_inst_4365_);
return v___f_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* v_00_u03b1_4367_, lean_object* v_inst_4368_){
_start:
{
lean_object* v___f_4369_; 
v___f_4369_ = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4369_, 0, v_inst_4368_);
return v___f_4369_;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t v___x_4370_, lean_object* v_k_4371_){
_start:
{
lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4372_ = ((lean_object*)(l_Lean_expandMacros___lam__0___closed__4));
v___x_4373_ = lean_name_eq(v_k_4371_, v___x_4372_);
if (v___x_4373_ == 0)
{
uint8_t v___x_4374_; 
v___x_4374_ = 1;
return v___x_4374_;
}
else
{
return v___x_4370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* v___x_4375_, lean_object* v_k_4376_){
_start:
{
uint8_t v___x_441__boxed_4377_; uint8_t v_res_4378_; lean_object* v_r_4379_; 
v___x_441__boxed_4377_ = lean_unbox(v___x_4375_);
v_res_4378_ = l_Lean_evalPrec___lam__0(v___x_441__boxed_4377_, v_k_4376_);
lean_dec(v_k_4376_);
v_r_4379_ = lean_box(v_res_4378_);
return v_r_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* v_stx_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v_methods_4384_; lean_object* v_quotContext_4385_; lean_object* v_currMacroScope_4386_; lean_object* v_currRecDepth_4387_; lean_object* v_maxRecDepth_4388_; lean_object* v_ref_4389_; uint8_t v___x_4390_; 
v_methods_4384_ = lean_ctor_get(v_a_4382_, 0);
v_quotContext_4385_ = lean_ctor_get(v_a_4382_, 1);
v_currMacroScope_4386_ = lean_ctor_get(v_a_4382_, 2);
v_currRecDepth_4387_ = lean_ctor_get(v_a_4382_, 3);
v_maxRecDepth_4388_ = lean_ctor_get(v_a_4382_, 4);
v_ref_4389_ = lean_ctor_get(v_a_4382_, 5);
v___x_4390_ = lean_nat_dec_eq(v_currRecDepth_4387_, v_maxRecDepth_4388_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v___f_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4391_ = lean_box(v___x_4390_);
v___f_4392_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4392_, 0, v___x_4391_);
v___x_4393_ = lean_unsigned_to_nat(1u);
v___x_4394_ = lean_nat_add(v_currRecDepth_4387_, v___x_4393_);
lean_inc(v_ref_4389_);
lean_inc(v_maxRecDepth_4388_);
lean_inc(v_currMacroScope_4386_);
lean_inc(v_quotContext_4385_);
lean_inc(v_methods_4384_);
v___x_4395_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4395_, 0, v_methods_4384_);
lean_ctor_set(v___x_4395_, 1, v_quotContext_4385_);
lean_ctor_set(v___x_4395_, 2, v_currMacroScope_4386_);
lean_ctor_set(v___x_4395_, 3, v___x_4394_);
lean_ctor_set(v___x_4395_, 4, v_maxRecDepth_4388_);
lean_ctor_set(v___x_4395_, 5, v_ref_4389_);
lean_inc_ref(v___x_4395_);
v___x_4396_ = l_Lean_expandMacros(v_stx_4381_, v___f_4392_, v___x_4395_, v_a_4383_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4410_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
v_a_4398_ = lean_ctor_get(v___x_4396_, 1);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4400_ = v___x_4396_;
v_isShared_4401_ = v_isSharedCheck_4410_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_inc(v_a_4397_);
lean_dec(v___x_4396_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4410_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; uint8_t v___x_4403_; 
v___x_4402_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4397_);
v___x_4403_ = l_Lean_Syntax_isOfKind(v_a_4397_, v___x_4402_);
if (v___x_4403_ == 0)
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
lean_del_object(v___x_4400_);
v___x_4404_ = ((lean_object*)(l_Lean_evalPrec___closed__0));
v___x_4405_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4397_, v___x_4404_, v___x_4395_, v_a_4398_);
lean_dec_ref_known(v___x_4395_, 6);
lean_dec(v_a_4397_);
return v___x_4405_;
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4408_; 
lean_dec_ref_known(v___x_4395_, 6);
v___x_4406_ = l_Lean_TSyntax_getNat(v_a_4397_);
lean_dec(v_a_4397_);
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 0, v___x_4406_);
v___x_4408_ = v___x_4400_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_a_4398_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec_ref_known(v___x_4395_, 6);
v_a_4411_ = lean_ctor_get(v___x_4396_, 0);
v_a_4412_ = lean_ctor_get(v___x_4396_, 1);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4396_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_inc(v_a_4411_);
lean_dec(v___x_4396_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4411_);
lean_ctor_set(v_reuseFailAlloc_4418_, 1, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
else
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4420_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4421_, 0, v_stx_4381_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
lean_ctor_set(v___x_4422_, 1, v_a_4383_);
return v___x_4422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___boxed(lean_object* v_stx_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_evalPrec(v_stx_4423_, v_a_4424_, v_a_4425_);
lean_dec_ref(v_a_4424_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* v_stx_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_){
_start:
{
lean_object* v_methods_4431_; lean_object* v_quotContext_4432_; lean_object* v_currMacroScope_4433_; lean_object* v_currRecDepth_4434_; lean_object* v_maxRecDepth_4435_; lean_object* v_ref_4436_; uint8_t v___x_4437_; 
v_methods_4431_ = lean_ctor_get(v_a_4429_, 0);
v_quotContext_4432_ = lean_ctor_get(v_a_4429_, 1);
v_currMacroScope_4433_ = lean_ctor_get(v_a_4429_, 2);
v_currRecDepth_4434_ = lean_ctor_get(v_a_4429_, 3);
v_maxRecDepth_4435_ = lean_ctor_get(v_a_4429_, 4);
v_ref_4436_ = lean_ctor_get(v_a_4429_, 5);
v___x_4437_ = lean_nat_dec_eq(v_currRecDepth_4434_, v_maxRecDepth_4435_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; lean_object* v___f_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4438_ = lean_box(v___x_4437_);
v___f_4439_ = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4439_, 0, v___x_4438_);
v___x_4440_ = lean_unsigned_to_nat(1u);
v___x_4441_ = lean_nat_add(v_currRecDepth_4434_, v___x_4440_);
lean_inc(v_ref_4436_);
lean_inc(v_maxRecDepth_4435_);
lean_inc(v_currMacroScope_4433_);
lean_inc(v_quotContext_4432_);
lean_inc(v_methods_4431_);
v___x_4442_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4442_, 0, v_methods_4431_);
lean_ctor_set(v___x_4442_, 1, v_quotContext_4432_);
lean_ctor_set(v___x_4442_, 2, v_currMacroScope_4433_);
lean_ctor_set(v___x_4442_, 3, v___x_4441_);
lean_ctor_set(v___x_4442_, 4, v_maxRecDepth_4435_);
lean_ctor_set(v___x_4442_, 5, v_ref_4436_);
lean_inc_ref(v___x_4442_);
v___x_4443_ = l_Lean_expandMacros(v_stx_4428_, v___f_4439_, v___x_4442_, v_a_4430_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4457_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
v_a_4445_ = lean_ctor_get(v___x_4443_, 1);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4447_ = v___x_4443_;
v_isShared_4448_ = v_isSharedCheck_4457_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_inc(v_a_4444_);
lean_dec(v___x_4443_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4457_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4449_; uint8_t v___x_4450_; 
v___x_4449_ = ((lean_object*)(l_Lean_Syntax_mkNumLit___closed__1));
lean_inc(v_a_4444_);
v___x_4450_ = l_Lean_Syntax_isOfKind(v_a_4444_, v___x_4449_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; lean_object* v___x_4452_; 
lean_del_object(v___x_4447_);
v___x_4451_ = ((lean_object*)(l_Lean_evalPrio___closed__0));
v___x_4452_ = l_Lean_Macro_throwErrorAt___redArg(v_a_4444_, v___x_4451_, v___x_4442_, v_a_4445_);
lean_dec_ref_known(v___x_4442_, 6);
lean_dec(v_a_4444_);
return v___x_4452_;
}
else
{
lean_object* v___x_4453_; lean_object* v___x_4455_; 
lean_dec_ref_known(v___x_4442_, 6);
v___x_4453_ = l_Lean_TSyntax_getNat(v_a_4444_);
lean_dec(v_a_4444_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 0, v___x_4453_);
v___x_4455_ = v___x_4447_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4453_);
lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_a_4445_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
lean_object* v_a_4458_; lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_dec_ref_known(v___x_4442_, 6);
v_a_4458_ = lean_ctor_get(v___x_4443_, 0);
v_a_4459_ = lean_ctor_get(v___x_4443_, 1);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4443_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_inc(v_a_4458_);
lean_dec(v___x_4443_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4458_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4467_ = ((lean_object*)(l_Lean_expandMacros___closed__0));
v___x_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4468_, 0, v_stx_4428_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
v___x_4469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4468_);
lean_ctor_set(v___x_4469_, 1, v_a_4430_);
return v___x_4469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio___boxed(lean_object* v_stx_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_evalPrio(v_stx_4470_, v_a_4471_, v_a_4472_);
lean_dec_ref(v_a_4471_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* v_x_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_){
_start:
{
if (lean_obj_tag(v_x_4474_) == 0)
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4477_ = lean_unsigned_to_nat(1000u);
v___x_4478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
lean_ctor_set(v___x_4478_, 1, v_a_4476_);
return v___x_4478_;
}
else
{
lean_object* v_val_4479_; lean_object* v___x_4480_; 
v_val_4479_ = lean_ctor_get(v_x_4474_, 0);
lean_inc(v_val_4479_);
lean_dec_ref_known(v_x_4474_, 1);
v___x_4480_ = l_Lean_evalPrio(v_val_4479_, v_a_4475_, v_a_4476_);
return v___x_4480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio___boxed(lean_object* v_x_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_evalOptPrio(v_x_4481_, v_a_4482_, v_a_4483_);
lean_dec_ref(v_a_4482_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t v___x_4485_, lean_object* v_x1_4486_, lean_object* v_x2_4487_){
_start:
{
lean_object* v_fst_4488_; uint8_t v___x_4489_; 
v_fst_4488_ = lean_ctor_get(v_x1_4486_, 0);
v___x_4489_ = lean_unbox(v_fst_4488_);
if (v___x_4489_ == 0)
{
lean_object* v_snd_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4498_; 
lean_dec(v_x2_4487_);
v_snd_4490_ = lean_ctor_get(v_x1_4486_, 1);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_x1_4486_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v_x1_4486_, 0);
lean_dec(v_unused_4499_);
v___x_4492_ = v_x1_4486_;
v_isShared_4493_ = v_isSharedCheck_4498_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_snd_4490_);
lean_dec(v_x1_4486_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4498_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; lean_object* v___x_4496_; 
v___x_4494_ = lean_box(v___x_4485_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___x_4494_);
v___x_4496_ = v___x_4492_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_snd_4490_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
else
{
lean_object* v_snd_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4510_; 
v_snd_4500_ = lean_ctor_get(v_x1_4486_, 1);
v_isSharedCheck_4510_ = !lean_is_exclusive(v_x1_4486_);
if (v_isSharedCheck_4510_ == 0)
{
lean_object* v_unused_4511_; 
v_unused_4511_ = lean_ctor_get(v_x1_4486_, 0);
lean_dec(v_unused_4511_);
v___x_4502_ = v_x1_4486_;
v_isShared_4503_ = v_isSharedCheck_4510_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_snd_4500_);
lean_dec(v_x1_4486_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4510_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
uint8_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4504_ = 0;
v___x_4505_ = lean_array_push(v_snd_4500_, v_x2_4487_);
v___x_4506_ = lean_box(v___x_4504_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 1, v___x_4505_);
lean_ctor_set(v___x_4502_, 0, v___x_4506_);
v___x_4508_ = v___x_4502_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v___x_4505_);
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
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* v___x_4512_, lean_object* v_x1_4513_, lean_object* v_x2_4514_){
_start:
{
uint8_t v___x_87__boxed_4515_; lean_object* v_res_4516_; 
v___x_87__boxed_4515_ = lean_unbox(v___x_4512_);
v_res_4516_ = l_Array_getSepElems___redArg___lam__0(v___x_87__boxed_4515_, v_x1_4513_, v_x2_4514_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* v_as_4538_){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; 
v___x_4539_ = lean_unsigned_to_nat(0u);
v___x_4540_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4541_ = lean_array_get_size(v_as_4538_);
v___x_4542_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4543_ = lean_nat_dec_lt(v___x_4539_, v___x_4541_);
if (v___x_4543_ == 0)
{
lean_dec_ref(v_as_4538_);
return v___x_4540_;
}
else
{
lean_object* v___x_4544_; lean_object* v___f_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; size_t v___x_4548_; size_t v___x_4549_; lean_object* v___x_4550_; lean_object* v_snd_4551_; 
v___x_4544_ = lean_box(v___x_4543_);
v___f_4545_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4545_, 0, v___x_4544_);
v___x_4546_ = lean_box(v___x_4543_);
v___x_4547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
lean_ctor_set(v___x_4547_, 1, v___x_4540_);
v___x_4548_ = ((size_t)0ULL);
v___x_4549_ = lean_usize_of_nat(v___x_4541_);
v___x_4550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4542_, v___f_4545_, v_as_4538_, v___x_4548_, v___x_4549_, v___x_4547_);
v_snd_4551_ = lean_ctor_get(v___x_4550_, 1);
lean_inc(v_snd_4551_);
lean_dec(v___x_4550_);
return v_snd_4551_;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* v_00_u03b1_4552_, lean_object* v_as_4553_){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; uint8_t v___x_4558_; 
v___x_4554_ = lean_unsigned_to_nat(0u);
v___x_4555_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__0));
v___x_4556_ = lean_array_get_size(v_as_4553_);
v___x_4557_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v___x_4558_ = lean_nat_dec_lt(v___x_4554_, v___x_4556_);
if (v___x_4558_ == 0)
{
lean_dec_ref(v_as_4553_);
return v___x_4555_;
}
else
{
lean_object* v___x_4559_; lean_object* v___f_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; size_t v___x_4563_; size_t v___x_4564_; lean_object* v___x_4565_; lean_object* v_snd_4566_; 
v___x_4559_ = lean_box(v___x_4558_);
v___f_4560_ = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4560_, 0, v___x_4559_);
v___x_4561_ = lean_box(v___x_4558_);
v___x_4562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
lean_ctor_set(v___x_4562_, 1, v___x_4555_);
v___x_4563_ = ((size_t)0ULL);
v___x_4564_ = lean_usize_of_nat(v___x_4556_);
v___x_4565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4557_, v___f_4560_, v_as_4553_, v___x_4563_, v___x_4564_, v___x_4562_);
v_snd_4566_ = lean_ctor_get(v___x_4565_, 1);
lean_inc(v_snd_4566_);
lean_dec(v___x_4565_);
return v_snd_4566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* v_i_4567_, lean_object* v_inst_4568_, lean_object* v_a_4569_, lean_object* v_p_4570_, lean_object* v_acc_4571_, lean_object* v_stx_4572_, uint8_t v_____do__lift_4573_){
_start:
{
if (v_____do__lift_4573_ == 0)
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
lean_dec(v_stx_4572_);
v___x_4582_ = lean_unsigned_to_nat(2u);
v___x_4583_ = lean_nat_add(v_i_4567_, v___x_4582_);
v___x_4584_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4568_, v_a_4569_, v_p_4570_, v___x_4583_, v_acc_4571_);
return v___x_4584_;
}
else
{
lean_object* v___x_4585_; lean_object* v___x_4586_; uint8_t v___x_4587_; 
v___x_4585_ = lean_array_get_size(v_acc_4571_);
v___x_4586_ = lean_unsigned_to_nat(0u);
v___x_4587_ = lean_nat_dec_eq(v___x_4585_, v___x_4586_);
if (v___x_4587_ == 0)
{
uint8_t v___x_4588_; 
v___x_4588_ = lean_nat_dec_eq(v_i_4567_, v___x_4586_);
if (v___x_4588_ == 0)
{
goto v___jp_4574_;
}
else
{
if (v___x_4587_ == 0)
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4589_ = lean_unsigned_to_nat(2u);
v___x_4590_ = lean_nat_add(v_i_4567_, v___x_4589_);
v___x_4591_ = lean_array_push(v_acc_4571_, v_stx_4572_);
v___x_4592_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4568_, v_a_4569_, v_p_4570_, v___x_4590_, v___x_4591_);
return v___x_4592_;
}
else
{
goto v___jp_4574_;
}
}
}
else
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4593_ = lean_unsigned_to_nat(2u);
v___x_4594_ = lean_nat_add(v_i_4567_, v___x_4593_);
v___x_4595_ = lean_array_push(v_acc_4571_, v_stx_4572_);
v___x_4596_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4568_, v_a_4569_, v_p_4570_, v___x_4594_, v___x_4595_);
return v___x_4596_;
}
}
v___jp_4574_:
{
lean_object* v___x_4575_; lean_object* v_sepStx_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4575_ = lean_nat_pred(v_i_4567_);
v_sepStx_4576_ = lean_array_fget_borrowed(v_a_4569_, v___x_4575_);
lean_dec(v___x_4575_);
v___x_4577_ = lean_unsigned_to_nat(2u);
v___x_4578_ = lean_nat_add(v_i_4567_, v___x_4577_);
lean_inc(v_sepStx_4576_);
v___x_4579_ = lean_array_push(v_acc_4571_, v_sepStx_4576_);
v___x_4580_ = lean_array_push(v___x_4579_, v_stx_4572_);
v___x_4581_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4568_, v_a_4569_, v_p_4570_, v___x_4578_, v___x_4580_);
return v___x_4581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4597_, lean_object* v_inst_4598_, lean_object* v_a_4599_, lean_object* v_p_4600_, lean_object* v_acc_4601_, lean_object* v_stx_4602_, lean_object* v_____do__lift_4603_){
_start:
{
uint8_t v_____do__lift_208__boxed_4604_; lean_object* v_res_4605_; 
v_____do__lift_208__boxed_4604_ = lean_unbox(v_____do__lift_4603_);
v_res_4605_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(v_i_4597_, v_inst_4598_, v_a_4599_, v_p_4600_, v_acc_4601_, v_stx_4602_, v_____do__lift_208__boxed_4604_);
lean_dec(v_i_4597_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* v_inst_4606_, lean_object* v_a_4607_, lean_object* v_p_4608_, lean_object* v_i_4609_, lean_object* v_acc_4610_){
_start:
{
lean_object* v_toApplicative_4611_; lean_object* v_toBind_4612_; lean_object* v_toPure_4613_; lean_object* v___x_4614_; uint8_t v___x_4615_; 
v_toApplicative_4611_ = lean_ctor_get(v_inst_4606_, 0);
v_toBind_4612_ = lean_ctor_get(v_inst_4606_, 1);
lean_inc(v_toBind_4612_);
v_toPure_4613_ = lean_ctor_get(v_toApplicative_4611_, 1);
v___x_4614_ = lean_array_get_size(v_a_4607_);
v___x_4615_ = lean_nat_dec_lt(v_i_4609_, v___x_4614_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; 
lean_inc(v_toPure_4613_);
lean_dec(v_toBind_4612_);
lean_dec(v_i_4609_);
lean_dec(v_p_4608_);
lean_dec_ref(v_a_4607_);
lean_dec_ref(v_inst_4606_);
v___x_4616_ = lean_apply_2(v_toPure_4613_, lean_box(0), v_acc_4610_);
return v___x_4616_;
}
else
{
lean_object* v_stx_4617_; lean_object* v___f_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v_stx_4617_ = lean_array_fget(v_a_4607_, v_i_4609_);
lean_inc(v_stx_4617_);
lean_inc(v_p_4608_);
v___f_4618_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_4618_, 0, v_i_4609_);
lean_closure_set(v___f_4618_, 1, v_inst_4606_);
lean_closure_set(v___f_4618_, 2, v_a_4607_);
lean_closure_set(v___f_4618_, 3, v_p_4608_);
lean_closure_set(v___f_4618_, 4, v_acc_4610_);
lean_closure_set(v___f_4618_, 5, v_stx_4617_);
v___x_4619_ = lean_apply_1(v_p_4608_, v_stx_4617_);
v___x_4620_ = lean_apply_4(v_toBind_4612_, lean_box(0), lean_box(0), v___x_4619_, v___f_4618_);
return v___x_4620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* v_m_4621_, lean_object* v_inst_4622_, lean_object* v_a_4623_, lean_object* v_p_4624_, lean_object* v_i_4625_, lean_object* v_acc_4626_){
_start:
{
lean_object* v___x_4627_; 
v___x_4627_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4622_, v_a_4623_, v_p_4624_, v_i_4625_, v_acc_4626_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* v_inst_4628_, lean_object* v_a_4629_, lean_object* v_p_4630_){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = lean_unsigned_to_nat(0u);
v___x_4632_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4633_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(v_inst_4628_, v_a_4629_, v_p_4630_, v___x_4631_, v___x_4632_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* v_m_4634_, lean_object* v_inst_4635_, lean_object* v_a_4636_, lean_object* v_p_4637_){
_start:
{
lean_object* v___x_4638_; 
v___x_4638_ = l_Array_filterSepElemsM___redArg(v_inst_4635_, v_a_4636_, v_p_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* v_p_4639_, lean_object* v_x_4640_){
_start:
{
lean_object* v___x_4641_; uint8_t v___x_4642_; 
v___x_4641_ = lean_apply_1(v_p_4639_, v_x_4640_);
v___x_4642_ = lean_unbox(v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* v_p_4643_, lean_object* v_x_4644_){
_start:
{
uint8_t v_res_4645_; lean_object* v_r_4646_; 
v_res_4645_ = l_Array_filterSepElems___lam__0(v_p_4643_, v_x_4644_);
v_r_4646_ = lean_box(v_res_4645_);
return v_r_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* v_a_4647_, lean_object* v_p_4648_, lean_object* v_i_4649_, lean_object* v_acc_4650_){
_start:
{
lean_object* v___x_4651_; uint8_t v___x_4652_; 
v___x_4651_ = lean_array_get_size(v_a_4647_);
v___x_4652_ = lean_nat_dec_lt(v_i_4649_, v___x_4651_);
if (v___x_4652_ == 0)
{
lean_dec(v_i_4649_);
lean_dec_ref(v_p_4648_);
return v_acc_4650_;
}
else
{
lean_object* v_stx_4653_; lean_object* v___x_4662_; uint8_t v___x_4663_; 
v_stx_4653_ = lean_array_fget_borrowed(v_a_4647_, v_i_4649_);
lean_inc_ref(v_p_4648_);
lean_inc(v_stx_4653_);
v___x_4662_ = lean_apply_1(v_p_4648_, v_stx_4653_);
v___x_4663_ = lean_unbox(v___x_4662_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4664_ = lean_unsigned_to_nat(2u);
v___x_4665_ = lean_nat_add(v_i_4649_, v___x_4664_);
lean_dec(v_i_4649_);
v_i_4649_ = v___x_4665_;
goto _start;
}
else
{
lean_object* v___x_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; 
v___x_4667_ = lean_array_get_size(v_acc_4650_);
v___x_4668_ = lean_unsigned_to_nat(0u);
v___x_4669_ = lean_nat_dec_eq(v___x_4667_, v___x_4668_);
if (v___x_4669_ == 0)
{
uint8_t v___x_4670_; 
v___x_4670_ = lean_nat_dec_eq(v_i_4649_, v___x_4668_);
if (v___x_4670_ == 0)
{
goto v___jp_4654_;
}
else
{
if (v___x_4669_ == 0)
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = lean_unsigned_to_nat(2u);
v___x_4672_ = lean_nat_add(v_i_4649_, v___x_4671_);
lean_dec(v_i_4649_);
lean_inc(v_stx_4653_);
v___x_4673_ = lean_array_push(v_acc_4650_, v_stx_4653_);
v_i_4649_ = v___x_4672_;
v_acc_4650_ = v___x_4673_;
goto _start;
}
else
{
goto v___jp_4654_;
}
}
}
else
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = lean_unsigned_to_nat(2u);
v___x_4676_ = lean_nat_add(v_i_4649_, v___x_4675_);
lean_dec(v_i_4649_);
lean_inc(v_stx_4653_);
v___x_4677_ = lean_array_push(v_acc_4650_, v_stx_4653_);
v_i_4649_ = v___x_4676_;
v_acc_4650_ = v___x_4677_;
goto _start;
}
}
v___jp_4654_:
{
lean_object* v___x_4655_; lean_object* v_sepStx_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4655_ = lean_nat_pred(v_i_4649_);
v_sepStx_4656_ = lean_array_fget_borrowed(v_a_4647_, v___x_4655_);
lean_dec(v___x_4655_);
v___x_4657_ = lean_unsigned_to_nat(2u);
v___x_4658_ = lean_nat_add(v_i_4649_, v___x_4657_);
lean_dec(v_i_4649_);
lean_inc(v_sepStx_4656_);
v___x_4659_ = lean_array_push(v_acc_4650_, v_sepStx_4656_);
lean_inc(v_stx_4653_);
v___x_4660_ = lean_array_push(v___x_4659_, v_stx_4653_);
v_i_4649_ = v___x_4658_;
v_acc_4650_ = v___x_4660_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* v_a_4679_, lean_object* v_p_4680_, lean_object* v_i_4681_, lean_object* v_acc_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4679_, v_p_4680_, v_i_4681_, v_acc_4682_);
lean_dec_ref(v_a_4679_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* v_a_4684_, lean_object* v_p_4685_){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = lean_unsigned_to_nat(0u);
v___x_4687_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4688_ = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(v_a_4684_, v_p_4685_, v___x_4686_, v___x_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* v_a_4689_, lean_object* v_p_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4689_, v_p_4690_);
lean_dec_ref(v_a_4689_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* v_a_4692_, lean_object* v_p_4693_){
_start:
{
lean_object* v___f_4694_; lean_object* v___x_4695_; 
v___f_4694_ = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4694_, 0, v_p_4693_);
v___x_4695_ = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(v_a_4692_, v___f_4694_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* v_a_4696_, lean_object* v_p_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l_Array_filterSepElems(v_a_4696_, v_p_4697_);
lean_dec_ref(v_a_4696_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* v_i_4699_, lean_object* v_acc_4700_, lean_object* v_inst_4701_, lean_object* v_a_4702_, lean_object* v_f_4703_, lean_object* v_stx_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(v_i_4699_, v_acc_4700_, v_inst_4701_, v_a_4702_, v_f_4703_, v_stx_4704_);
lean_dec(v_i_4699_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* v_inst_4706_, lean_object* v_a_4707_, lean_object* v_f_4708_, lean_object* v_i_4709_, lean_object* v_acc_4710_){
_start:
{
lean_object* v_toApplicative_4711_; lean_object* v_toBind_4712_; lean_object* v_toPure_4713_; lean_object* v___x_4714_; uint8_t v___x_4715_; 
v_toApplicative_4711_ = lean_ctor_get(v_inst_4706_, 0);
v_toBind_4712_ = lean_ctor_get(v_inst_4706_, 1);
v_toPure_4713_ = lean_ctor_get(v_toApplicative_4711_, 1);
v___x_4714_ = lean_array_get_size(v_a_4707_);
v___x_4715_ = lean_nat_dec_lt(v_i_4709_, v___x_4714_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; 
lean_inc(v_toPure_4713_);
lean_dec(v_i_4709_);
lean_dec(v_f_4708_);
lean_dec_ref(v_a_4707_);
lean_dec_ref(v_inst_4706_);
v___x_4716_ = lean_apply_2(v_toPure_4713_, lean_box(0), v_acc_4710_);
return v___x_4716_;
}
else
{
lean_object* v_stx_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; uint8_t v___x_4721_; 
v_stx_4717_ = lean_array_fget_borrowed(v_a_4707_, v_i_4709_);
v___x_4718_ = lean_unsigned_to_nat(2u);
v___x_4719_ = lean_nat_mod(v_i_4709_, v___x_4718_);
v___x_4720_ = lean_unsigned_to_nat(0u);
v___x_4721_ = lean_nat_dec_eq(v___x_4719_, v___x_4720_);
lean_dec(v___x_4719_);
if (v___x_4721_ == 0)
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4722_ = lean_unsigned_to_nat(1u);
v___x_4723_ = lean_nat_add(v_i_4709_, v___x_4722_);
lean_dec(v_i_4709_);
lean_inc(v_stx_4717_);
v___x_4724_ = lean_array_push(v_acc_4710_, v_stx_4717_);
v_i_4709_ = v___x_4723_;
v_acc_4710_ = v___x_4724_;
goto _start;
}
else
{
lean_object* v___f_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
lean_inc(v_stx_4717_);
lean_inc(v_toBind_4712_);
lean_inc(v_f_4708_);
v___f_4726_ = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_4726_, 0, v_i_4709_);
lean_closure_set(v___f_4726_, 1, v_acc_4710_);
lean_closure_set(v___f_4726_, 2, v_inst_4706_);
lean_closure_set(v___f_4726_, 3, v_a_4707_);
lean_closure_set(v___f_4726_, 4, v_f_4708_);
v___x_4727_ = lean_apply_1(v_f_4708_, v_stx_4717_);
v___x_4728_ = lean_apply_4(v_toBind_4712_, lean_box(0), lean_box(0), v___x_4727_, v___f_4726_);
return v___x_4728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* v_i_4729_, lean_object* v_acc_4730_, lean_object* v_inst_4731_, lean_object* v_a_4732_, lean_object* v_f_4733_, lean_object* v_stx_4734_){
_start:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4735_ = lean_unsigned_to_nat(1u);
v___x_4736_ = lean_nat_add(v_i_4729_, v___x_4735_);
v___x_4737_ = lean_array_push(v_acc_4730_, v_stx_4734_);
v___x_4738_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4731_, v_a_4732_, v_f_4733_, v___x_4736_, v___x_4737_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* v_m_4739_, lean_object* v_inst_4740_, lean_object* v_a_4741_, lean_object* v_f_4742_, lean_object* v_i_4743_, lean_object* v_acc_4744_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4740_, v_a_4741_, v_f_4742_, v_i_4743_, v_acc_4744_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* v_inst_4746_, lean_object* v_a_4747_, lean_object* v_f_4748_){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4749_ = lean_unsigned_to_nat(0u);
v___x_4750_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4751_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(v_inst_4746_, v_a_4747_, v_f_4748_, v___x_4749_, v___x_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* v_m_4752_, lean_object* v_inst_4753_, lean_object* v_a_4754_, lean_object* v_f_4755_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l_Array_mapSepElemsM___redArg(v_inst_4753_, v_a_4754_, v_f_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* v_f_4757_, lean_object* v_x_4758_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = lean_apply_1(v_f_4757_, v_x_4758_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* v_a_4760_, lean_object* v_f_4761_, lean_object* v_i_4762_, lean_object* v_acc_4763_){
_start:
{
lean_object* v___x_4764_; uint8_t v___x_4765_; 
v___x_4764_ = lean_array_get_size(v_a_4760_);
v___x_4765_ = lean_nat_dec_lt(v_i_4762_, v___x_4764_);
if (v___x_4765_ == 0)
{
lean_dec(v_i_4762_);
lean_dec_ref(v_f_4761_);
return v_acc_4763_;
}
else
{
lean_object* v_stx_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; uint8_t v___x_4770_; 
v_stx_4766_ = lean_array_fget_borrowed(v_a_4760_, v_i_4762_);
v___x_4767_ = lean_unsigned_to_nat(2u);
v___x_4768_ = lean_nat_mod(v_i_4762_, v___x_4767_);
v___x_4769_ = lean_unsigned_to_nat(0u);
v___x_4770_ = lean_nat_dec_eq(v___x_4768_, v___x_4769_);
lean_dec(v___x_4768_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4771_ = lean_unsigned_to_nat(1u);
v___x_4772_ = lean_nat_add(v_i_4762_, v___x_4771_);
lean_dec(v_i_4762_);
lean_inc(v_stx_4766_);
v___x_4773_ = lean_array_push(v_acc_4763_, v_stx_4766_);
v_i_4762_ = v___x_4772_;
v_acc_4763_ = v___x_4773_;
goto _start;
}
else
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
lean_inc_ref(v_f_4761_);
lean_inc(v_stx_4766_);
v___x_4775_ = lean_apply_1(v_f_4761_, v_stx_4766_);
v___x_4776_ = lean_unsigned_to_nat(1u);
v___x_4777_ = lean_nat_add(v_i_4762_, v___x_4776_);
lean_dec(v_i_4762_);
v___x_4778_ = lean_array_push(v_acc_4763_, v___x_4775_);
v_i_4762_ = v___x_4777_;
v_acc_4763_ = v___x_4778_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* v_a_4780_, lean_object* v_f_4781_, lean_object* v_i_4782_, lean_object* v_acc_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4780_, v_f_4781_, v_i_4782_, v_acc_4783_);
lean_dec_ref(v_a_4780_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* v_a_4785_, lean_object* v_f_4786_){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4787_ = lean_unsigned_to_nat(0u);
v___x_4788_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
v___x_4789_ = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(v_a_4785_, v_f_4786_, v___x_4787_, v___x_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* v_a_4790_, lean_object* v_f_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4790_, v_f_4791_);
lean_dec_ref(v_a_4790_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* v_a_4793_, lean_object* v_f_4794_){
_start:
{
lean_object* v___f_4795_; lean_object* v___x_4796_; 
v___f_4795_ = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(v___f_4795_, 0, v_f_4794_);
v___x_4796_ = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(v_a_4793_, v___f_4795_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* v_a_4797_, lean_object* v_f_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Array_mapSepElems(v_a_4797_, v_f_4798_);
lean_dec_ref(v_a_4797_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* v_as_4800_, size_t v_i_4801_, size_t v_stop_4802_, lean_object* v_b_4803_){
_start:
{
lean_object* v___y_4805_; uint8_t v___x_4809_; 
v___x_4809_ = lean_usize_dec_eq(v_i_4801_, v_stop_4802_);
if (v___x_4809_ == 0)
{
lean_object* v_fst_4810_; uint8_t v___x_4811_; 
v_fst_4810_ = lean_ctor_get(v_b_4803_, 0);
v___x_4811_ = lean_unbox(v_fst_4810_);
if (v___x_4811_ == 0)
{
lean_object* v_snd_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4821_; 
v_snd_4812_ = lean_ctor_get(v_b_4803_, 1);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_b_4803_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; 
v_unused_4822_ = lean_ctor_get(v_b_4803_, 0);
lean_dec(v_unused_4822_);
v___x_4814_ = v_b_4803_;
v_isShared_4815_ = v_isSharedCheck_4821_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_snd_4812_);
lean_dec(v_b_4803_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4821_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
uint8_t v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4819_; 
v___x_4816_ = 1;
v___x_4817_ = lean_box(v___x_4816_);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 0, v___x_4817_);
v___x_4819_ = v___x_4814_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4817_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_snd_4812_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
v___y_4805_ = v___x_4819_;
goto v___jp_4804_;
}
}
}
else
{
lean_object* v_snd_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4833_; 
v_snd_4823_ = lean_ctor_get(v_b_4803_, 1);
v_isSharedCheck_4833_ = !lean_is_exclusive(v_b_4803_);
if (v_isSharedCheck_4833_ == 0)
{
lean_object* v_unused_4834_; 
v_unused_4834_ = lean_ctor_get(v_b_4803_, 0);
lean_dec(v_unused_4834_);
v___x_4825_ = v_b_4803_;
v_isShared_4826_ = v_isSharedCheck_4833_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_snd_4823_);
lean_dec(v_b_4803_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4833_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4831_; 
v___x_4827_ = lean_array_uget_borrowed(v_as_4800_, v_i_4801_);
lean_inc(v___x_4827_);
v___x_4828_ = lean_array_push(v_snd_4823_, v___x_4827_);
v___x_4829_ = lean_box(v___x_4809_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 1, v___x_4828_);
lean_ctor_set(v___x_4825_, 0, v___x_4829_);
v___x_4831_ = v___x_4825_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4829_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v___x_4828_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
v___y_4805_ = v___x_4831_;
goto v___jp_4804_;
}
}
}
}
else
{
return v_b_4803_;
}
v___jp_4804_:
{
size_t v___x_4806_; size_t v___x_4807_; 
v___x_4806_ = ((size_t)1ULL);
v___x_4807_ = lean_usize_add(v_i_4801_, v___x_4806_);
v_i_4801_ = v___x_4807_;
v_b_4803_ = v___y_4805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* v_as_4835_, lean_object* v_i_4836_, lean_object* v_stop_4837_, lean_object* v_b_4838_){
_start:
{
size_t v_i_boxed_4839_; size_t v_stop_boxed_4840_; lean_object* v_res_4841_; 
v_i_boxed_4839_ = lean_unbox_usize(v_i_4836_);
lean_dec(v_i_4836_);
v_stop_boxed_4840_ = lean_unbox_usize(v_stop_4837_);
lean_dec(v_stop_4837_);
v_res_4841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_as_4835_, v_i_boxed_4839_, v_stop_boxed_4840_, v_b_4838_);
lean_dec_ref(v_as_4835_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* v_sa_4842_){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; uint8_t v___x_4846_; 
v___x_4843_ = lean_unsigned_to_nat(0u);
v___x_4844_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4845_ = lean_array_get_size(v_sa_4842_);
v___x_4846_ = lean_nat_dec_lt(v___x_4843_, v___x_4845_);
if (v___x_4846_ == 0)
{
return v___x_4844_;
}
else
{
lean_object* v___x_4847_; lean_object* v___x_4848_; size_t v___x_4849_; size_t v___x_4850_; lean_object* v___x_4851_; lean_object* v_snd_4852_; 
v___x_4847_ = lean_box(v___x_4846_);
v___x_4848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
lean_ctor_set(v___x_4848_, 1, v___x_4844_);
v___x_4849_ = ((size_t)0ULL);
v___x_4850_ = lean_usize_of_nat(v___x_4845_);
v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4842_, v___x_4849_, v___x_4850_, v___x_4848_);
v_snd_4852_ = lean_ctor_get(v___x_4851_, 1);
lean_inc(v_snd_4852_);
lean_dec_ref(v___x_4851_);
return v_snd_4852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* v_sa_4853_){
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4853_);
lean_dec_ref(v_sa_4853_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* v_sep_4855_, lean_object* v_sa_4856_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lean_Syntax_SepArray_getElems___redArg(v_sa_4856_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* v_sep_4858_, lean_object* v_sa_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l_Lean_Syntax_SepArray_getElems(v_sep_4858_, v_sa_4859_);
lean_dec_ref(v_sa_4859_);
lean_dec_ref(v_sep_4858_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* v_sa_4861_){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; 
v___x_4862_ = lean_unsigned_to_nat(0u);
v___x_4863_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_4864_ = lean_array_get_size(v_sa_4861_);
v___x_4865_ = lean_nat_dec_lt(v___x_4862_, v___x_4864_);
if (v___x_4865_ == 0)
{
return v___x_4863_;
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; size_t v___x_4868_; size_t v___x_4869_; lean_object* v___x_4870_; lean_object* v_snd_4871_; 
v___x_4866_ = lean_box(v___x_4865_);
v___x_4867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4866_);
lean_ctor_set(v___x_4867_, 1, v___x_4863_);
v___x_4868_ = ((size_t)0ULL);
v___x_4869_ = lean_usize_of_nat(v___x_4864_);
v___x_4870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v_sa_4861_, v___x_4868_, v___x_4869_, v___x_4867_);
v_snd_4871_ = lean_ctor_get(v___x_4870_, 1);
lean_inc(v_snd_4871_);
lean_dec_ref(v___x_4870_);
return v_snd_4871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* v_sa_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4872_);
lean_dec_ref(v_sa_4872_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* v_k_4874_, lean_object* v_sep_4875_, lean_object* v_sa_4876_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_sa_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* v_k_4878_, lean_object* v_sep_4879_, lean_object* v_sa_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l_Lean_Syntax_TSepArray_getElems(v_k_4878_, v_sep_4879_, v_sa_4880_);
lean_dec_ref(v_sa_4880_);
lean_dec_ref(v_sep_4879_);
lean_dec(v_k_4878_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* v_sep_4882_, lean_object* v_sa_4883_, lean_object* v_e_4884_){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4885_ = lean_array_get_size(v_sa_4883_);
v___x_4886_ = lean_unsigned_to_nat(0u);
v___x_4887_ = lean_nat_dec_eq(v___x_4885_, v___x_4886_);
if (v___x_4887_ == 0)
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4888_ = l_Lean_mkAtom(v_sep_4882_);
v___x_4889_ = lean_array_push(v_sa_4883_, v___x_4888_);
v___x_4890_ = lean_array_push(v___x_4889_, v_e_4884_);
return v___x_4890_;
}
else
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
lean_dec_ref(v_sa_4883_);
lean_dec_ref(v_sep_4882_);
v___x_4891_ = lean_unsigned_to_nat(1u);
v___x_4892_ = lean_mk_empty_array_with_capacity(v___x_4891_);
v___x_4893_ = lean_array_push(v___x_4892_, v_e_4884_);
return v___x_4893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* v_k_4894_, lean_object* v_sep_4895_, lean_object* v_sa_4896_, lean_object* v_e_4897_){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l_Lean_Syntax_TSepArray_push___redArg(v_sep_4895_, v_sa_4896_, v_e_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* v_k_4899_, lean_object* v_sep_4900_, lean_object* v_sa_4901_, lean_object* v_e_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l_Lean_Syntax_TSepArray_push(v_k_4899_, v_sep_4900_, v_sa_4901_, v_e_4902_);
lean_dec(v_k_4899_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* v_sep_4904_){
_start:
{
lean_object* v___x_4905_; 
v___x_4905_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* v_sep_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l_Lean_Syntax_instEmptyCollectionSepArray(v_sep_4906_);
lean_dec_ref(v_sep_4906_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* v_sep_4908_, lean_object* v_k_4909_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* v_sep_4911_, lean_object* v_k_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Lean_Syntax_instEmptyCollectionTSepArray(v_sep_4911_, v_k_4912_);
lean_dec_ref(v_k_4912_);
lean_dec(v_sep_4911_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___lam__0(lean_object* v_v_4914_){
_start:
{
lean_inc_ref(v_v_4914_);
return v_v_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___lam__0___boxed(lean_object* v_v_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Lean_Syntax_instCoeOutTSepArraySepArray___lam__0(v_v_4915_);
lean_dec_ref(v_v_4915_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray(lean_object* v_k_4918_, lean_object* v_sep_4919_){
_start:
{
lean_object* v___f_4920_; 
v___f_4920_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSepArraySepArray___closed__0));
return v___f_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArraySepArray___boxed(lean_object* v_k_4921_, lean_object* v_sep_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Lean_Syntax_instCoeOutTSepArraySepArray(v_k_4921_, v_sep_4922_);
lean_dec_ref(v_sep_4922_);
lean_dec(v_k_4921_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* v_k_4924_, lean_object* v_sep_4925_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(v___x_4926_, 0, v_k_4924_);
lean_closure_set(v___x_4926_, 1, v_sep_4925_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* v_inst_4927_, lean_object* v_x_4928_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = lean_apply_1(v_inst_4927_, v_x_4928_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* v___f_4930_, lean_object* v_a_4931_){
_start:
{
lean_object* v___x_4932_; size_t v_sz_4933_; size_t v___x_4934_; lean_object* v___x_4935_; 
v___x_4932_ = ((lean_object*)(l_Array_getSepElems___redArg___closed__10));
v_sz_4933_ = lean_array_size(v_a_4931_);
v___x_4934_ = ((size_t)0ULL);
v___x_4935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_4932_, v___f_4930_, v_sz_4933_, v___x_4934_, v_a_4931_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* v_inst_4936_){
_start:
{
lean_object* v___f_4937_; lean_object* v___f_4938_; 
v___f_4937_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4937_, 0, v_inst_4936_);
v___f_4938_ = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4938_, 0, v___f_4937_);
return v___f_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* v_k_4939_, lean_object* v_k_x27_4940_, lean_object* v_inst_4941_){
_start:
{
lean_object* v___x_4942_; 
v___x_4942_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(v_inst_4941_);
return v___x_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* v_k_4943_, lean_object* v_k_x27_4944_, lean_object* v_inst_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(v_k_4943_, v_k_x27_4944_, v_inst_4945_);
lean_dec(v_k_x27_4944_);
lean_dec(v_k_4943_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object* v_a_4947_){
_start:
{
lean_inc_ref(v_a_4947_);
return v_a_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object* v_a_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(v_a_4948_);
lean_dec_ref(v_a_4948_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* v_k_4951_){
_start:
{
lean_object* v___f_4952_; 
v___f_4952_ = ((lean_object*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0));
return v___f_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* v_k_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(v_k_4953_);
lean_dec(v_k_4953_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* v_id_4962_){
_start:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4963_ = ((lean_object*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2));
v___x_4964_ = lean_box(2);
v___x_4965_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__2));
v___x_4966_ = lean_unsigned_to_nat(2u);
v___x_4967_ = lean_mk_empty_array_with_capacity(v___x_4966_);
v___x_4968_ = lean_array_push(v___x_4967_, v_id_4962_);
v___x_4969_ = lean_array_push(v___x_4968_, v___x_4965_);
v___x_4970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4964_);
lean_ctor_set(v___x_4970_, 1, v___x_4963_);
lean_ctor_set(v___x_4970_, 2, v___x_4969_);
return v___x_4970_;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1(void){
_start:
{
uint32_t v___x_4974_; lean_object* v___x_4975_; 
v___x_4974_ = 123;
v___x_4975_ = lean_box_uint32(v___x_4974_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* v_s_4976_, lean_object* v_i_4977_){
_start:
{
lean_object* v___x_4978_; 
v___x_4978_ = l_Lean_Syntax_decodeQuotedChar(v_s_4976_, v_i_4977_);
if (lean_obj_tag(v___x_4978_) == 0)
{
uint32_t v_c_4979_; uint32_t v___x_4980_; uint8_t v___x_4981_; 
v_c_4979_ = lean_string_utf8_get(v_s_4976_, v_i_4977_);
v___x_4980_ = 123;
v___x_4981_ = lean_uint32_dec_eq(v_c_4979_, v___x_4980_);
if (v___x_4981_ == 0)
{
return v___x_4978_;
}
else
{
lean_object* v_i_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v_i_4982_ = lean_string_utf8_next(v_s_4976_, v_i_4977_);
v___x_4983_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
v___x_4984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
lean_ctor_set(v___x_4984_, 1, v_i_4982_);
v___x_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4984_);
return v___x_4985_;
}
}
else
{
return v___x_4978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* v_s_4986_, lean_object* v_i_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_4986_, v_i_4987_);
lean_dec(v_i_4987_);
lean_dec_ref(v_s_4986_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* v_s_4989_, lean_object* v_i_4990_, lean_object* v_acc_4991_){
_start:
{
uint32_t v_c_4992_; uint32_t v___x_4993_; uint8_t v___x_4994_; 
v_c_4992_ = lean_string_utf8_get(v_s_4989_, v_i_4990_);
v___x_4993_ = 34;
v___x_4994_ = lean_uint32_dec_eq(v_c_4992_, v___x_4993_);
if (v___x_4994_ == 0)
{
uint32_t v___x_4995_; uint8_t v___x_4996_; 
v___x_4995_ = 123;
v___x_4996_ = lean_uint32_dec_eq(v_c_4992_, v___x_4995_);
if (v___x_4996_ == 0)
{
lean_object* v_i_4997_; uint8_t v___x_4998_; 
v_i_4997_ = lean_string_utf8_next(v_s_4989_, v_i_4990_);
lean_dec(v_i_4990_);
v___x_4998_ = lean_string_utf8_at_end(v_s_4989_, v_i_4997_);
if (v___x_4998_ == 0)
{
uint32_t v___x_4999_; uint8_t v___x_5000_; 
v___x_4999_ = 92;
v___x_5000_ = lean_uint32_dec_eq(v_c_4992_, v___x_4999_);
if (v___x_5000_ == 0)
{
lean_object* v___x_5001_; 
v___x_5001_ = lean_string_push(v_acc_4991_, v_c_4992_);
v_i_4990_ = v_i_4997_;
v_acc_4991_ = v___x_5001_;
goto _start;
}
else
{
lean_object* v___x_5003_; 
v___x_5003_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(v_s_4989_, v_i_4997_);
if (lean_obj_tag(v___x_5003_) == 1)
{
lean_object* v_val_5004_; lean_object* v_fst_5005_; lean_object* v_snd_5006_; uint32_t v___x_5007_; lean_object* v___x_5008_; 
lean_dec(v_i_4997_);
v_val_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_val_5004_);
lean_dec_ref_known(v___x_5003_, 1);
v_fst_5005_ = lean_ctor_get(v_val_5004_, 0);
lean_inc(v_fst_5005_);
v_snd_5006_ = lean_ctor_get(v_val_5004_, 1);
lean_inc(v_snd_5006_);
lean_dec(v_val_5004_);
v___x_5007_ = lean_unbox_uint32(v_fst_5005_);
lean_dec(v_fst_5005_);
v___x_5008_ = lean_string_push(v_acc_4991_, v___x_5007_);
v_i_4990_ = v_snd_5006_;
v_acc_4991_ = v___x_5008_;
goto _start;
}
else
{
lean_object* v___x_5010_; 
lean_dec(v___x_5003_);
lean_inc_ref(v_s_4989_);
v___x_5010_ = l_Lean_Syntax_decodeStringGap(v_s_4989_, v_i_4997_);
lean_dec(v_i_4997_);
if (lean_obj_tag(v___x_5010_) == 1)
{
lean_object* v_val_5011_; 
v_val_5011_ = lean_ctor_get(v___x_5010_, 0);
lean_inc(v_val_5011_);
lean_dec_ref_known(v___x_5010_, 1);
v_i_4990_ = v_val_5011_;
goto _start;
}
else
{
lean_object* v___x_5013_; 
lean_dec(v___x_5010_);
lean_dec_ref(v_acc_4991_);
lean_dec_ref(v_s_4989_);
v___x_5013_ = lean_box(0);
return v___x_5013_;
}
}
}
}
else
{
lean_object* v___x_5014_; 
lean_dec(v_i_4997_);
lean_dec_ref(v_acc_4991_);
lean_dec_ref(v_s_4989_);
v___x_5014_ = lean_box(0);
return v___x_5014_;
}
}
else
{
lean_object* v___x_5015_; 
lean_dec(v_i_4990_);
lean_dec_ref(v_s_4989_);
v___x_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5015_, 0, v_acc_4991_);
return v___x_5015_;
}
}
else
{
lean_object* v___x_5016_; 
lean_dec(v_i_4990_);
lean_dec_ref(v_s_4989_);
v___x_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5016_, 0, v_acc_4991_);
return v___x_5016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* v_s_5017_){
_start:
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5018_ = lean_unsigned_to_nat(1u);
v___x_5019_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5020_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(v_s_5017_, v___x_5018_, v___x_5019_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* v_stx_5024_){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5025_ = ((lean_object*)(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1));
v___x_5026_ = l_Lean_Syntax_isLit_x3f(v___x_5025_, v_stx_5024_);
if (lean_obj_tag(v___x_5026_) == 0)
{
return v___x_5026_;
}
else
{
lean_object* v_val_5027_; lean_object* v___x_5028_; 
v_val_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc(v_val_5027_);
lean_dec_ref_known(v___x_5026_, 1);
v___x_5028_ = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(v_val_5027_);
return v___x_5028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* v_stx_5029_){
_start:
{
lean_object* v_res_5030_; 
v_res_5030_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_stx_5029_);
lean_dec(v_stx_5029_);
return v_res_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* v_stx_5031_){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; uint8_t v___x_5036_; 
v___x_5032_ = l_Lean_Syntax_getArgs(v_stx_5031_);
v___x_5033_ = lean_unsigned_to_nat(0u);
v___x_5034_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_5035_ = lean_array_get_size(v___x_5032_);
v___x_5036_ = lean_nat_dec_lt(v___x_5033_, v___x_5035_);
if (v___x_5036_ == 0)
{
lean_dec_ref(v___x_5032_);
return v___x_5034_;
}
else
{
lean_object* v___x_5037_; lean_object* v___x_5038_; size_t v___x_5039_; size_t v___x_5040_; lean_object* v___x_5041_; lean_object* v_snd_5042_; 
v___x_5037_ = lean_box(v___x_5036_);
v___x_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5037_);
lean_ctor_set(v___x_5038_, 1, v___x_5034_);
v___x_5039_ = ((size_t)0ULL);
v___x_5040_ = lean_usize_of_nat(v___x_5035_);
v___x_5041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(v___x_5032_, v___x_5039_, v___x_5040_, v___x_5038_);
lean_dec_ref(v___x_5032_);
v_snd_5042_ = lean_ctor_get(v___x_5041_, 1);
lean_inc(v_snd_5042_);
lean_dec_ref(v___x_5041_);
return v_snd_5042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* v_stx_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_Syntax_getSepArgs(v_stx_5043_);
lean_dec(v_stx_5043_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* v_mkAppend_5045_, lean_object* v_mkElem_5046_, lean_object* v_mkLit_5047_, lean_object* v_as_5048_, size_t v_sz_5049_, size_t v_i_5050_, lean_object* v_b_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v_a_5055_; lean_object* v_a_5056_; lean_object* v_elem_5061_; lean_object* v___y_5062_; lean_object* v___y_5063_; uint8_t v___x_5068_; 
v___x_5068_ = lean_usize_dec_lt(v_i_5050_, v_sz_5049_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; 
lean_dec_ref(v_mkLit_5047_);
lean_dec_ref(v_mkElem_5046_);
lean_dec_ref(v_mkAppend_5045_);
v___x_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5069_, 0, v_b_5051_);
lean_ctor_set(v___x_5069_, 1, v___y_5053_);
return v___x_5069_;
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5071_; 
v_a_5070_ = lean_array_uget_borrowed(v_as_5048_, v_i_5050_);
v___x_5071_ = l_Lean_Syntax_isInterpolatedStrLit_x3f(v_a_5070_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_object* v_methods_5072_; lean_object* v_quotContext_5073_; lean_object* v_currMacroScope_5074_; lean_object* v_currRecDepth_5075_; lean_object* v_maxRecDepth_5076_; lean_object* v_ref_5077_; lean_object* v_ref_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
v_methods_5072_ = lean_ctor_get(v___y_5052_, 0);
v_quotContext_5073_ = lean_ctor_get(v___y_5052_, 1);
v_currMacroScope_5074_ = lean_ctor_get(v___y_5052_, 2);
v_currRecDepth_5075_ = lean_ctor_get(v___y_5052_, 3);
v_maxRecDepth_5076_ = lean_ctor_get(v___y_5052_, 4);
v_ref_5077_ = lean_ctor_get(v___y_5052_, 5);
v_ref_5078_ = l_Lean_replaceRef(v_a_5070_, v_ref_5077_);
lean_inc(v_maxRecDepth_5076_);
lean_inc(v_currRecDepth_5075_);
lean_inc(v_currMacroScope_5074_);
lean_inc(v_quotContext_5073_);
lean_inc(v_methods_5072_);
v___x_5079_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5079_, 0, v_methods_5072_);
lean_ctor_set(v___x_5079_, 1, v_quotContext_5073_);
lean_ctor_set(v___x_5079_, 2, v_currMacroScope_5074_);
lean_ctor_set(v___x_5079_, 3, v_currRecDepth_5075_);
lean_ctor_set(v___x_5079_, 4, v_maxRecDepth_5076_);
lean_ctor_set(v___x_5079_, 5, v_ref_5078_);
lean_inc_ref(v_mkElem_5046_);
lean_inc(v_a_5070_);
v___x_5080_ = lean_apply_3(v_mkElem_5046_, v_a_5070_, v___x_5079_, v___y_5053_);
if (lean_obj_tag(v___x_5080_) == 0)
{
lean_object* v_a_5081_; lean_object* v_a_5082_; 
v_a_5081_ = lean_ctor_get(v___x_5080_, 0);
lean_inc(v_a_5081_);
v_a_5082_ = lean_ctor_get(v___x_5080_, 1);
lean_inc(v_a_5082_);
lean_dec_ref_known(v___x_5080_, 2);
v_elem_5061_ = v_a_5081_;
v___y_5062_ = v___y_5052_;
v___y_5063_ = v_a_5082_;
goto v___jp_5060_;
}
else
{
lean_dec(v_b_5051_);
lean_dec_ref(v_mkLit_5047_);
lean_dec_ref(v_mkElem_5046_);
lean_dec_ref(v_mkAppend_5045_);
return v___x_5080_;
}
}
else
{
lean_object* v_val_5083_; uint8_t v___x_5084_; 
v_val_5083_ = lean_ctor_get(v___x_5071_, 0);
lean_inc_n(v_val_5083_, 2);
lean_dec_ref_known(v___x_5071_, 1);
v___x_5084_ = lean_string_isempty(v_val_5083_);
if (v___x_5084_ == 0)
{
lean_object* v_methods_5085_; lean_object* v_quotContext_5086_; lean_object* v_currMacroScope_5087_; lean_object* v_currRecDepth_5088_; lean_object* v_maxRecDepth_5089_; lean_object* v_ref_5090_; lean_object* v_ref_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v_methods_5085_ = lean_ctor_get(v___y_5052_, 0);
v_quotContext_5086_ = lean_ctor_get(v___y_5052_, 1);
v_currMacroScope_5087_ = lean_ctor_get(v___y_5052_, 2);
v_currRecDepth_5088_ = lean_ctor_get(v___y_5052_, 3);
v_maxRecDepth_5089_ = lean_ctor_get(v___y_5052_, 4);
v_ref_5090_ = lean_ctor_get(v___y_5052_, 5);
v_ref_5091_ = l_Lean_replaceRef(v_a_5070_, v_ref_5090_);
lean_inc(v_maxRecDepth_5089_);
lean_inc(v_currRecDepth_5088_);
lean_inc(v_currMacroScope_5087_);
lean_inc(v_quotContext_5086_);
lean_inc(v_methods_5085_);
v___x_5092_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5092_, 0, v_methods_5085_);
lean_ctor_set(v___x_5092_, 1, v_quotContext_5086_);
lean_ctor_set(v___x_5092_, 2, v_currMacroScope_5087_);
lean_ctor_set(v___x_5092_, 3, v_currRecDepth_5088_);
lean_ctor_set(v___x_5092_, 4, v_maxRecDepth_5089_);
lean_ctor_set(v___x_5092_, 5, v_ref_5091_);
lean_inc_ref(v_mkLit_5047_);
v___x_5093_ = lean_apply_3(v_mkLit_5047_, v_val_5083_, v___x_5092_, v___y_5053_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; lean_object* v_a_5095_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_a_5094_);
v_a_5095_ = lean_ctor_get(v___x_5093_, 1);
lean_inc(v_a_5095_);
lean_dec_ref_known(v___x_5093_, 2);
v_elem_5061_ = v_a_5094_;
v___y_5062_ = v___y_5052_;
v___y_5063_ = v_a_5095_;
goto v___jp_5060_;
}
else
{
lean_dec(v_b_5051_);
lean_dec_ref(v_mkLit_5047_);
lean_dec_ref(v_mkElem_5046_);
lean_dec_ref(v_mkAppend_5045_);
return v___x_5093_;
}
}
else
{
lean_dec(v_val_5083_);
v_a_5055_ = v_b_5051_;
v_a_5056_ = v___y_5053_;
goto v___jp_5054_;
}
}
}
v___jp_5054_:
{
size_t v___x_5057_; size_t v___x_5058_; 
v___x_5057_ = ((size_t)1ULL);
v___x_5058_ = lean_usize_add(v_i_5050_, v___x_5057_);
v_i_5050_ = v___x_5058_;
v_b_5051_ = v_a_5055_;
v___y_5053_ = v_a_5056_;
goto _start;
}
v___jp_5060_:
{
uint8_t v___x_5064_; 
v___x_5064_ = l_Lean_Syntax_isMissing(v_b_5051_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5065_; 
lean_inc_ref(v_mkAppend_5045_);
lean_inc_ref(v___y_5062_);
v___x_5065_ = lean_apply_4(v_mkAppend_5045_, v_b_5051_, v_elem_5061_, v___y_5062_, v___y_5063_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; lean_object* v_a_5067_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
v_a_5067_ = lean_ctor_get(v___x_5065_, 1);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5065_, 2);
v_a_5055_ = v_a_5066_;
v_a_5056_ = v_a_5067_;
goto v___jp_5054_;
}
else
{
lean_dec_ref(v_mkLit_5047_);
lean_dec_ref(v_mkElem_5046_);
lean_dec_ref(v_mkAppend_5045_);
return v___x_5065_;
}
}
else
{
lean_dec(v_b_5051_);
v_a_5055_ = v_elem_5061_;
v_a_5056_ = v___y_5063_;
goto v___jp_5054_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* v_mkAppend_5096_, lean_object* v_mkElem_5097_, lean_object* v_mkLit_5098_, lean_object* v_as_5099_, lean_object* v_sz_5100_, lean_object* v_i_5101_, lean_object* v_b_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
size_t v_sz_boxed_5105_; size_t v_i_boxed_5106_; lean_object* v_res_5107_; 
v_sz_boxed_5105_ = lean_unbox_usize(v_sz_5100_);
lean_dec(v_sz_5100_);
v_i_boxed_5106_ = lean_unbox_usize(v_i_5101_);
lean_dec(v_i_5101_);
v_res_5107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5096_, v_mkElem_5097_, v_mkLit_5098_, v_as_5099_, v_sz_boxed_5105_, v_i_boxed_5106_, v_b_5102_, v___y_5103_, v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec_ref(v_as_5099_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* v_chunks_5108_, lean_object* v_mkAppend_5109_, lean_object* v_mkElem_5110_, lean_object* v_mkLit_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_result_5114_; size_t v_sz_5115_; size_t v___x_5116_; lean_object* v___x_5117_; 
v_result_5114_ = lean_box(0);
v_sz_5115_ = lean_array_size(v_chunks_5108_);
v___x_5116_ = ((size_t)0ULL);
lean_inc_ref(v_mkLit_5111_);
v___x_5117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(v_mkAppend_5109_, v_mkElem_5110_, v_mkLit_5111_, v_chunks_5108_, v_sz_5115_, v___x_5116_, v_result_5114_, v_a_5112_, v_a_5113_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v_a_5119_; uint8_t v___x_5120_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_a_5118_);
v_a_5119_ = lean_ctor_get(v___x_5117_, 1);
lean_inc(v_a_5119_);
v___x_5120_ = l_Lean_Syntax_isMissing(v_a_5118_);
lean_dec(v_a_5118_);
if (v___x_5120_ == 0)
{
lean_dec(v_a_5119_);
lean_dec_ref(v_mkLit_5111_);
return v___x_5117_;
}
else
{
lean_object* v___x_5121_; lean_object* v___x_5122_; 
lean_dec_ref_known(v___x_5117_, 2);
v___x_5121_ = ((lean_object*)(l_Lean_versionString___closed__0));
lean_inc_ref(v_a_5112_);
v___x_5122_ = lean_apply_3(v_mkLit_5111_, v___x_5121_, v_a_5112_, v_a_5119_);
return v___x_5122_;
}
}
else
{
lean_dec_ref(v_mkLit_5111_);
return v___x_5117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* v_chunks_5123_, lean_object* v_mkAppend_5124_, lean_object* v_mkElem_5125_, lean_object* v_mkLit_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v_res_5129_; 
v_res_5129_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v_chunks_5123_, v_mkAppend_5124_, v_mkElem_5125_, v_mkLit_5126_, v_a_5127_, v_a_5128_);
lean_dec_ref(v_a_5127_);
lean_dec_ref(v_chunks_5123_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* v_a_5134_, lean_object* v_b_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_){
_start:
{
lean_object* v_ref_5138_; uint8_t v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v_ref_5138_ = lean_ctor_get(v___y_5136_, 5);
v___x_5139_ = 0;
v___x_5140_ = l_Lean_SourceInfo_fromRef(v_ref_5138_, v___x_5139_);
v___x_5141_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1));
v___x_5142_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2));
lean_inc(v___x_5140_);
v___x_5143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5140_);
lean_ctor_set(v___x_5143_, 1, v___x_5142_);
v___x_5144_ = l_Lean_Syntax_node3(v___x_5140_, v___x_5141_, v_a_5134_, v___x_5143_, v_b_5135_);
v___x_5145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5144_);
lean_ctor_set(v___x_5145_, 1, v___y_5137_);
return v___x_5145_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* v_a_5146_, lean_object* v_b_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_TSyntax_expandInterpolatedStr___lam__0(v_a_5146_, v_b_5147_, v___y_5148_, v___y_5149_);
lean_dec_ref(v___y_5148_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* v_ofInterpFn_5151_, lean_object* v_a_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v_ref_5155_; uint8_t v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v_ref_5155_ = lean_ctor_get(v___y_5153_, 5);
v___x_5156_ = 0;
v___x_5157_ = l_Lean_SourceInfo_fromRef(v_ref_5155_, v___x_5156_);
v___x_5158_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5159_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v___x_5157_);
v___x_5160_ = l_Lean_Syntax_node1(v___x_5157_, v___x_5159_, v_a_5152_);
v___x_5161_ = l_Lean_Syntax_node2(v___x_5157_, v___x_5158_, v_ofInterpFn_5151_, v___x_5160_);
v___x_5162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5161_);
lean_ctor_set(v___x_5162_, 1, v___y_5154_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* v_ofInterpFn_5163_, lean_object* v_a_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_TSyntax_expandInterpolatedStr___lam__1(v_ofInterpFn_5163_, v_a_5164_, v___y_5165_, v___y_5166_);
lean_dec_ref(v___y_5165_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* v_ofLitFn_5168_, lean_object* v_s_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v_ref_5172_; uint8_t v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
v_ref_5172_ = lean_ctor_get(v___y_5170_, 5);
v___x_5173_ = 0;
v___x_5174_ = l_Lean_SourceInfo_fromRef(v_ref_5172_, v___x_5173_);
v___x_5175_ = ((lean_object*)(l_Lean_Syntax_mkApp___closed__1));
v___x_5176_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5177_ = lean_box(2);
v___x_5178_ = l_Lean_Syntax_mkStrLit(v_s_5169_, v___x_5177_);
lean_inc(v___x_5174_);
v___x_5179_ = l_Lean_Syntax_node1(v___x_5174_, v___x_5176_, v___x_5178_);
v___x_5180_ = l_Lean_Syntax_node2(v___x_5174_, v___x_5175_, v_ofLitFn_5168_, v___x_5179_);
v___x_5181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5180_);
lean_ctor_set(v___x_5181_, 1, v___y_5171_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* v_ofLitFn_5182_, lean_object* v_s_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_Lean_TSyntax_expandInterpolatedStr___lam__2(v_ofLitFn_5182_, v_s_5183_, v___y_5184_, v___y_5185_);
lean_dec_ref(v___y_5184_);
return v_res_5186_;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8(void){
_start:
{
lean_object* v___x_5204_; lean_object* v___x_5205_; 
v___x_5204_ = ((lean_object*)(l_Lean_versionString___closed__0));
v___x_5205_ = l_String_toRawSubstring_x27(v___x_5204_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* v_interpStr_5226_, lean_object* v_type_5227_, lean_object* v_ofInterpFn_5228_, lean_object* v_ofLitFn_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_){
_start:
{
lean_object* v___f_5232_; lean_object* v___f_5233_; lean_object* v___f_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___f_5232_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__0));
v___f_5233_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5233_, 0, v_ofInterpFn_5228_);
v___f_5234_ = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(v___f_5234_, 0, v_ofLitFn_5229_);
v___x_5235_ = l_Lean_Syntax_getArgs(v_interpStr_5226_);
v___x_5236_ = l_Lean_TSyntax_expandInterpolatedStrChunks(v___x_5235_, v___f_5232_, v___f_5233_, v___f_5234_, v_a_5230_, v_a_5231_);
lean_dec_ref(v___x_5235_);
if (lean_obj_tag(v___x_5236_) == 0)
{
lean_object* v_a_5237_; lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5269_; 
v_a_5237_ = lean_ctor_get(v___x_5236_, 0);
v_a_5238_ = lean_ctor_get(v___x_5236_, 1);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5236_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5240_ = v___x_5236_;
v_isShared_5241_ = v_isSharedCheck_5269_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_inc(v_a_5237_);
lean_dec(v___x_5236_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5269_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v_quotContext_5242_; lean_object* v_currMacroScope_5243_; lean_object* v_ref_5244_; uint8_t v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5267_; 
v_quotContext_5242_ = lean_ctor_get(v_a_5230_, 1);
v_currMacroScope_5243_ = lean_ctor_get(v_a_5230_, 2);
v_ref_5244_ = lean_ctor_get(v_a_5230_, 5);
v___x_5245_ = 0;
v___x_5246_ = l_Lean_SourceInfo_fromRef(v_ref_5244_, v___x_5245_);
v___x_5247_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__2));
v___x_5248_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__4));
v___x_5249_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__5));
lean_inc_n(v___x_5246_, 7);
v___x_5250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5246_);
lean_ctor_set(v___x_5250_, 1, v___x_5249_);
v___x_5251_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__7));
v___x_5252_ = lean_obj_once(&l_Lean_TSyntax_expandInterpolatedStr___closed__8, &l_Lean_TSyntax_expandInterpolatedStr___closed__8_once, _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8);
v___x_5253_ = lean_box(0);
lean_inc(v_currMacroScope_5243_);
lean_inc(v_quotContext_5242_);
v___x_5254_ = l_Lean_addMacroScope(v_quotContext_5242_, v___x_5253_, v_currMacroScope_5243_);
v___x_5255_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__16));
v___x_5256_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5256_, 0, v___x_5246_);
lean_ctor_set(v___x_5256_, 1, v___x_5252_);
lean_ctor_set(v___x_5256_, 2, v___x_5254_);
lean_ctor_set(v___x_5256_, 3, v___x_5255_);
v___x_5257_ = l_Lean_Syntax_node1(v___x_5246_, v___x_5251_, v___x_5256_);
v___x_5258_ = l_Lean_Syntax_node2(v___x_5246_, v___x_5248_, v___x_5250_, v___x_5257_);
v___x_5259_ = ((lean_object*)(l_Lean_toolchain___closed__0));
v___x_5260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5246_);
lean_ctor_set(v___x_5260_, 1, v___x_5259_);
v___x_5261_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_5262_ = l_Lean_Syntax_node1(v___x_5246_, v___x_5261_, v_type_5227_);
v___x_5263_ = ((lean_object*)(l_Lean_TSyntax_expandInterpolatedStr___closed__17));
v___x_5264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5246_);
lean_ctor_set(v___x_5264_, 1, v___x_5263_);
v___x_5265_ = l_Lean_Syntax_node5(v___x_5246_, v___x_5247_, v___x_5258_, v_a_5237_, v___x_5260_, v___x_5262_, v___x_5264_);
if (v_isShared_5241_ == 0)
{
lean_ctor_set(v___x_5240_, 0, v___x_5265_);
v___x_5267_ = v___x_5240_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5265_);
lean_ctor_set(v_reuseFailAlloc_5268_, 1, v_a_5238_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
else
{
lean_object* v_a_5270_; lean_object* v_a_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5278_; 
lean_dec(v_type_5227_);
v_a_5270_ = lean_ctor_get(v___x_5236_, 0);
v_a_5271_ = lean_ctor_get(v___x_5236_, 1);
v_isSharedCheck_5278_ = !lean_is_exclusive(v___x_5236_);
if (v_isSharedCheck_5278_ == 0)
{
v___x_5273_ = v___x_5236_;
v_isShared_5274_ = v_isSharedCheck_5278_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_a_5271_);
lean_inc(v_a_5270_);
lean_dec(v___x_5236_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5278_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___x_5276_; 
if (v_isShared_5274_ == 0)
{
v___x_5276_ = v___x_5273_;
goto v_reusejp_5275_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5270_);
lean_ctor_set(v_reuseFailAlloc_5277_, 1, v_a_5271_);
v___x_5276_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5275_;
}
v_reusejp_5275_:
{
return v___x_5276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* v_interpStr_5279_, lean_object* v_type_5280_, lean_object* v_ofInterpFn_5281_, lean_object* v_ofLitFn_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_5279_, v_type_5280_, v_ofInterpFn_5281_, v_ofLitFn_5282_, v_a_5283_, v_a_5284_);
lean_dec_ref(v_a_5283_);
lean_dec(v_interpStr_5279_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* v_stx_5286_){
_start:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = lean_unsigned_to_nat(1u);
v___x_5288_ = l_Lean_Syntax_getArg(v_stx_5286_, v___x_5287_);
if (lean_obj_tag(v___x_5288_) == 2)
{
lean_object* v_val_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v_val_5289_ = lean_ctor_get(v___x_5288_, 1);
lean_inc_ref(v_val_5289_);
lean_dec_ref_known(v___x_5288_, 2);
v___x_5290_ = lean_unsigned_to_nat(0u);
v___x_5291_ = lean_string_utf8_byte_size(v_val_5289_);
v___x_5292_ = lean_unsigned_to_nat(2u);
v___x_5293_ = lean_string_pos_sub(v___x_5291_, v___x_5292_);
v___x_5294_ = lean_string_utf8_extract(v_val_5289_, v___x_5290_, v___x_5293_);
lean_dec(v___x_5293_);
lean_dec_ref(v_val_5289_);
return v___x_5294_;
}
else
{
lean_object* v___x_5295_; 
lean_dec(v___x_5288_);
v___x_5295_ = ((lean_object*)(l_Lean_versionString___closed__0));
return v___x_5295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* v_stx_5296_){
_start:
{
lean_object* v_res_5297_; 
v_res_5297_ = l_Lean_TSyntax_getDocString(v_stx_5296_);
lean_dec(v_stx_5296_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t v_x_5316_, lean_object* v_prec_5317_){
_start:
{
lean_object* v___y_5319_; lean_object* v___y_5326_; lean_object* v___y_5333_; lean_object* v___y_5340_; lean_object* v___y_5347_; lean_object* v___y_5354_; 
switch(v_x_5316_)
{
case 0:
{
lean_object* v___x_5360_; uint8_t v___x_5361_; 
v___x_5360_ = lean_unsigned_to_nat(1024u);
v___x_5361_ = lean_nat_dec_le(v___x_5360_, v_prec_5317_);
if (v___x_5361_ == 0)
{
lean_object* v___x_5362_; 
v___x_5362_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5319_ = v___x_5362_;
goto v___jp_5318_;
}
else
{
lean_object* v___x_5363_; 
v___x_5363_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5319_ = v___x_5363_;
goto v___jp_5318_;
}
}
case 1:
{
lean_object* v___x_5364_; uint8_t v___x_5365_; 
v___x_5364_ = lean_unsigned_to_nat(1024u);
v___x_5365_ = lean_nat_dec_le(v___x_5364_, v_prec_5317_);
if (v___x_5365_ == 0)
{
lean_object* v___x_5366_; 
v___x_5366_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5326_ = v___x_5366_;
goto v___jp_5325_;
}
else
{
lean_object* v___x_5367_; 
v___x_5367_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5326_ = v___x_5367_;
goto v___jp_5325_;
}
}
case 2:
{
lean_object* v___x_5368_; uint8_t v___x_5369_; 
v___x_5368_ = lean_unsigned_to_nat(1024u);
v___x_5369_ = lean_nat_dec_le(v___x_5368_, v_prec_5317_);
if (v___x_5369_ == 0)
{
lean_object* v___x_5370_; 
v___x_5370_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5333_ = v___x_5370_;
goto v___jp_5332_;
}
else
{
lean_object* v___x_5371_; 
v___x_5371_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5333_ = v___x_5371_;
goto v___jp_5332_;
}
}
case 3:
{
lean_object* v___x_5372_; uint8_t v___x_5373_; 
v___x_5372_ = lean_unsigned_to_nat(1024u);
v___x_5373_ = lean_nat_dec_le(v___x_5372_, v_prec_5317_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; 
v___x_5374_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5340_ = v___x_5374_;
goto v___jp_5339_;
}
else
{
lean_object* v___x_5375_; 
v___x_5375_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5340_ = v___x_5375_;
goto v___jp_5339_;
}
}
case 4:
{
lean_object* v___x_5376_; uint8_t v___x_5377_; 
v___x_5376_ = lean_unsigned_to_nat(1024u);
v___x_5377_ = lean_nat_dec_le(v___x_5376_, v_prec_5317_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5378_; 
v___x_5378_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5347_ = v___x_5378_;
goto v___jp_5346_;
}
else
{
lean_object* v___x_5379_; 
v___x_5379_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5347_ = v___x_5379_;
goto v___jp_5346_;
}
}
default: 
{
lean_object* v___x_5380_; uint8_t v___x_5381_; 
v___x_5380_ = lean_unsigned_to_nat(1024u);
v___x_5381_ = lean_nat_dec_le(v___x_5380_, v_prec_5317_);
if (v___x_5381_ == 0)
{
lean_object* v___x_5382_; 
v___x_5382_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5354_ = v___x_5382_;
goto v___jp_5353_;
}
else
{
lean_object* v___x_5383_; 
v___x_5383_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5354_ = v___x_5383_;
goto v___jp_5353_;
}
}
}
v___jp_5318_:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; uint8_t v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___x_5320_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__1));
lean_inc(v___y_5319_);
v___x_5321_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___y_5319_);
lean_ctor_set(v___x_5321_, 1, v___x_5320_);
v___x_5322_ = 0;
v___x_5323_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5323_, 0, v___x_5321_);
lean_ctor_set_uint8(v___x_5323_, sizeof(void*)*1, v___x_5322_);
v___x_5324_ = l_Repr_addAppParen(v___x_5323_, v_prec_5317_);
return v___x_5324_;
}
v___jp_5325_:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; uint8_t v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
v___x_5327_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__3));
lean_inc(v___y_5326_);
v___x_5328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5328_, 0, v___y_5326_);
lean_ctor_set(v___x_5328_, 1, v___x_5327_);
v___x_5329_ = 0;
v___x_5330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5330_, 0, v___x_5328_);
lean_ctor_set_uint8(v___x_5330_, sizeof(void*)*1, v___x_5329_);
v___x_5331_ = l_Repr_addAppParen(v___x_5330_, v_prec_5317_);
return v___x_5331_;
}
v___jp_5332_:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; uint8_t v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5334_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__5));
lean_inc(v___y_5333_);
v___x_5335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5335_, 0, v___y_5333_);
lean_ctor_set(v___x_5335_, 1, v___x_5334_);
v___x_5336_ = 0;
v___x_5337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5337_, 0, v___x_5335_);
lean_ctor_set_uint8(v___x_5337_, sizeof(void*)*1, v___x_5336_);
v___x_5338_ = l_Repr_addAppParen(v___x_5337_, v_prec_5317_);
return v___x_5338_;
}
v___jp_5339_:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; uint8_t v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5341_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__7));
lean_inc(v___y_5340_);
v___x_5342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5342_, 0, v___y_5340_);
lean_ctor_set(v___x_5342_, 1, v___x_5341_);
v___x_5343_ = 0;
v___x_5344_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5344_, 0, v___x_5342_);
lean_ctor_set_uint8(v___x_5344_, sizeof(void*)*1, v___x_5343_);
v___x_5345_ = l_Repr_addAppParen(v___x_5344_, v_prec_5317_);
return v___x_5345_;
}
v___jp_5346_:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; uint8_t v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5348_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__9));
lean_inc(v___y_5347_);
v___x_5349_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5349_, 0, v___y_5347_);
lean_ctor_set(v___x_5349_, 1, v___x_5348_);
v___x_5350_ = 0;
v___x_5351_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5351_, 0, v___x_5349_);
lean_ctor_set_uint8(v___x_5351_, sizeof(void*)*1, v___x_5350_);
v___x_5352_ = l_Repr_addAppParen(v___x_5351_, v_prec_5317_);
return v___x_5352_;
}
v___jp_5353_:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; uint8_t v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5355_ = ((lean_object*)(l_Lean_Meta_instReprTransparencyMode_repr___closed__11));
lean_inc(v___y_5354_);
v___x_5356_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5356_, 0, v___y_5354_);
lean_ctor_set(v___x_5356_, 1, v___x_5355_);
v___x_5357_ = 0;
v___x_5358_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5358_, 0, v___x_5356_);
lean_ctor_set_uint8(v___x_5358_, sizeof(void*)*1, v___x_5357_);
v___x_5359_ = l_Repr_addAppParen(v___x_5358_, v_prec_5317_);
return v___x_5359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* v_x_5384_, lean_object* v_prec_5385_){
_start:
{
uint8_t v_x_329__boxed_5386_; lean_object* v_res_5387_; 
v_x_329__boxed_5386_ = lean_unbox(v_x_5384_);
v_res_5387_ = l_Lean_Meta_instReprTransparencyMode_repr(v_x_329__boxed_5386_, v_prec_5385_);
lean_dec(v_prec_5385_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t v_x_5399_, lean_object* v_prec_5400_){
_start:
{
lean_object* v___y_5402_; lean_object* v___y_5409_; lean_object* v___y_5416_; 
switch(v_x_5399_)
{
case 0:
{
lean_object* v___x_5422_; uint8_t v___x_5423_; 
v___x_5422_ = lean_unsigned_to_nat(1024u);
v___x_5423_ = lean_nat_dec_le(v___x_5422_, v_prec_5400_);
if (v___x_5423_ == 0)
{
lean_object* v___x_5424_; 
v___x_5424_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5402_ = v___x_5424_;
goto v___jp_5401_;
}
else
{
lean_object* v___x_5425_; 
v___x_5425_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5402_ = v___x_5425_;
goto v___jp_5401_;
}
}
case 1:
{
lean_object* v___x_5426_; uint8_t v___x_5427_; 
v___x_5426_ = lean_unsigned_to_nat(1024u);
v___x_5427_ = lean_nat_dec_le(v___x_5426_, v_prec_5400_);
if (v___x_5427_ == 0)
{
lean_object* v___x_5428_; 
v___x_5428_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5409_ = v___x_5428_;
goto v___jp_5408_;
}
else
{
lean_object* v___x_5429_; 
v___x_5429_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5409_ = v___x_5429_;
goto v___jp_5408_;
}
}
default: 
{
lean_object* v___x_5430_; uint8_t v___x_5431_; 
v___x_5430_ = lean_unsigned_to_nat(1024u);
v___x_5431_ = lean_nat_dec_le(v___x_5430_, v_prec_5400_);
if (v___x_5431_ == 0)
{
lean_object* v___x_5432_; 
v___x_5432_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__3, &l_Lean_Syntax_instReprPreresolved_repr___closed__3_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3);
v___y_5416_ = v___x_5432_;
goto v___jp_5415_;
}
else
{
lean_object* v___x_5433_; 
v___x_5433_ = lean_obj_once(&l_Lean_Syntax_instReprPreresolved_repr___closed__4, &l_Lean_Syntax_instReprPreresolved_repr___closed__4_once, _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4);
v___y_5416_ = v___x_5433_;
goto v___jp_5415_;
}
}
}
v___jp_5401_:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; uint8_t v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5403_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__1));
lean_inc(v___y_5402_);
v___x_5404_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5404_, 0, v___y_5402_);
lean_ctor_set(v___x_5404_, 1, v___x_5403_);
v___x_5405_ = 0;
v___x_5406_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5406_, 0, v___x_5404_);
lean_ctor_set_uint8(v___x_5406_, sizeof(void*)*1, v___x_5405_);
v___x_5407_ = l_Repr_addAppParen(v___x_5406_, v_prec_5400_);
return v___x_5407_;
}
v___jp_5408_:
{
lean_object* v___x_5410_; lean_object* v___x_5411_; uint8_t v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5410_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__3));
lean_inc(v___y_5409_);
v___x_5411_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___y_5409_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = 0;
v___x_5413_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5413_, 0, v___x_5411_);
lean_ctor_set_uint8(v___x_5413_, sizeof(void*)*1, v___x_5412_);
v___x_5414_ = l_Repr_addAppParen(v___x_5413_, v_prec_5400_);
return v___x_5414_;
}
v___jp_5415_:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; uint8_t v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5417_ = ((lean_object*)(l_Lean_Meta_instReprEtaStructMode_repr___closed__5));
lean_inc(v___y_5416_);
v___x_5418_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5418_, 0, v___y_5416_);
lean_ctor_set(v___x_5418_, 1, v___x_5417_);
v___x_5419_ = 0;
v___x_5420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5420_, 0, v___x_5418_);
lean_ctor_set_uint8(v___x_5420_, sizeof(void*)*1, v___x_5419_);
v___x_5421_ = l_Repr_addAppParen(v___x_5420_, v_prec_5400_);
return v___x_5421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* v_x_5434_, lean_object* v_prec_5435_){
_start:
{
uint8_t v_x_167__boxed_5436_; lean_object* v_res_5437_; 
v_x_167__boxed_5436_ = lean_unbox(v_x_5434_);
v_res_5437_ = l_Lean_Meta_instReprEtaStructMode_repr(v_x_167__boxed_5436_, v_prec_5435_);
lean_dec(v_prec_5435_);
return v_res_5437_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___x_5449_ = lean_unsigned_to_nat(8u);
v___x_5450_ = lean_nat_to_int(v___x_5449_);
return v___x_5450_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5460_ = lean_unsigned_to_nat(13u);
v___x_5461_ = lean_nat_to_int(v___x_5460_);
return v___x_5461_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = lean_unsigned_to_nat(10u);
v___x_5472_ = lean_nat_to_int(v___x_5471_);
return v___x_5472_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_5476_; lean_object* v___x_5477_; 
v___x_5476_ = lean_unsigned_to_nat(14u);
v___x_5477_ = lean_nat_to_int(v___x_5476_);
return v___x_5477_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5481_ = lean_unsigned_to_nat(19u);
v___x_5482_ = lean_nat_to_int(v___x_5481_);
return v___x_5482_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5486_ = lean_unsigned_to_nat(20u);
v___x_5487_ = lean_nat_to_int(v___x_5486_);
return v___x_5487_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = lean_unsigned_to_nat(9u);
v___x_5495_ = lean_nat_to_int(v___x_5494_);
return v___x_5495_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_5502_; lean_object* v___x_5503_; 
v___x_5502_ = lean_unsigned_to_nat(12u);
v___x_5503_ = lean_nat_to_int(v___x_5502_);
return v___x_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* v_x_5510_){
_start:
{
uint8_t v_zeta_5511_; uint8_t v_beta_5512_; uint8_t v_eta_5513_; uint8_t v_etaStruct_5514_; uint8_t v_iota_5515_; uint8_t v_proj_5516_; uint8_t v_decide_5517_; uint8_t v_autoUnfold_5518_; uint8_t v_failIfUnchanged_5519_; uint8_t v_unfoldPartialApp_5520_; uint8_t v_zetaDelta_5521_; uint8_t v_index_5522_; uint8_t v_zetaUnused_5523_; uint8_t v_zetaHave_5524_; uint8_t v_locals_5525_; uint8_t v_instances_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; 
v_zeta_5511_ = lean_ctor_get_uint8(v_x_5510_, 0);
v_beta_5512_ = lean_ctor_get_uint8(v_x_5510_, 1);
v_eta_5513_ = lean_ctor_get_uint8(v_x_5510_, 2);
v_etaStruct_5514_ = lean_ctor_get_uint8(v_x_5510_, 3);
v_iota_5515_ = lean_ctor_get_uint8(v_x_5510_, 4);
v_proj_5516_ = lean_ctor_get_uint8(v_x_5510_, 5);
v_decide_5517_ = lean_ctor_get_uint8(v_x_5510_, 6);
v_autoUnfold_5518_ = lean_ctor_get_uint8(v_x_5510_, 7);
v_failIfUnchanged_5519_ = lean_ctor_get_uint8(v_x_5510_, 8);
v_unfoldPartialApp_5520_ = lean_ctor_get_uint8(v_x_5510_, 9);
v_zetaDelta_5521_ = lean_ctor_get_uint8(v_x_5510_, 10);
v_index_5522_ = lean_ctor_get_uint8(v_x_5510_, 11);
v_zetaUnused_5523_ = lean_ctor_get_uint8(v_x_5510_, 12);
v_zetaHave_5524_ = lean_ctor_get_uint8(v_x_5510_, 13);
v_locals_5525_ = lean_ctor_get_uint8(v_x_5510_, 14);
v_instances_5526_ = lean_ctor_get_uint8(v_x_5510_, 15);
v___x_5527_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5528_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__3));
v___x_5529_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5530_ = lean_unsigned_to_nat(0u);
v___x_5531_ = l_Bool_repr___redArg(v_zeta_5511_);
v___x_5532_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5529_);
lean_ctor_set(v___x_5532_, 1, v___x_5531_);
v___x_5533_ = 0;
v___x_5534_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5534_, 0, v___x_5532_);
lean_ctor_set_uint8(v___x_5534_, sizeof(void*)*1, v___x_5533_);
v___x_5535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5535_, 0, v___x_5528_);
lean_ctor_set(v___x_5535_, 1, v___x_5534_);
v___x_5536_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5535_);
lean_ctor_set(v___x_5537_, 1, v___x_5536_);
v___x_5538_ = lean_box(1);
v___x_5539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5537_);
lean_ctor_set(v___x_5539_, 1, v___x_5538_);
v___x_5540_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5541_, 0, v___x_5539_);
lean_ctor_set(v___x_5541_, 1, v___x_5540_);
v___x_5542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5541_);
lean_ctor_set(v___x_5542_, 1, v___x_5527_);
v___x_5543_ = l_Bool_repr___redArg(v_beta_5512_);
v___x_5544_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5529_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
v___x_5545_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5545_, 0, v___x_5544_);
lean_ctor_set_uint8(v___x_5545_, sizeof(void*)*1, v___x_5533_);
v___x_5546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5542_);
lean_ctor_set(v___x_5546_, 1, v___x_5545_);
v___x_5547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5547_, 0, v___x_5546_);
lean_ctor_set(v___x_5547_, 1, v___x_5536_);
v___x_5548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5548_, 0, v___x_5547_);
lean_ctor_set(v___x_5548_, 1, v___x_5538_);
v___x_5549_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5548_);
lean_ctor_set(v___x_5550_, 1, v___x_5549_);
v___x_5551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5551_, 0, v___x_5550_);
lean_ctor_set(v___x_5551_, 1, v___x_5527_);
v___x_5552_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5553_ = l_Bool_repr___redArg(v_eta_5513_);
v___x_5554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5554_, 0, v___x_5552_);
lean_ctor_set(v___x_5554_, 1, v___x_5553_);
v___x_5555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5555_, 0, v___x_5554_);
lean_ctor_set_uint8(v___x_5555_, sizeof(void*)*1, v___x_5533_);
v___x_5556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5556_, 0, v___x_5551_);
lean_ctor_set(v___x_5556_, 1, v___x_5555_);
v___x_5557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5556_);
lean_ctor_set(v___x_5557_, 1, v___x_5536_);
v___x_5558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5557_);
lean_ctor_set(v___x_5558_, 1, v___x_5538_);
v___x_5559_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5560_, 0, v___x_5558_);
lean_ctor_set(v___x_5560_, 1, v___x_5559_);
v___x_5561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5561_, 0, v___x_5560_);
lean_ctor_set(v___x_5561_, 1, v___x_5527_);
v___x_5562_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5563_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5514_, v___x_5530_);
v___x_5564_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5562_);
lean_ctor_set(v___x_5564_, 1, v___x_5563_);
v___x_5565_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5565_, 0, v___x_5564_);
lean_ctor_set_uint8(v___x_5565_, sizeof(void*)*1, v___x_5533_);
v___x_5566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5561_);
lean_ctor_set(v___x_5566_, 1, v___x_5565_);
v___x_5567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5566_);
lean_ctor_set(v___x_5567_, 1, v___x_5536_);
v___x_5568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5567_);
lean_ctor_set(v___x_5568_, 1, v___x_5538_);
v___x_5569_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5568_);
lean_ctor_set(v___x_5570_, 1, v___x_5569_);
v___x_5571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5571_, 0, v___x_5570_);
lean_ctor_set(v___x_5571_, 1, v___x_5527_);
v___x_5572_ = l_Bool_repr___redArg(v_iota_5515_);
v___x_5573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5573_, 0, v___x_5529_);
lean_ctor_set(v___x_5573_, 1, v___x_5572_);
v___x_5574_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5574_, 0, v___x_5573_);
lean_ctor_set_uint8(v___x_5574_, sizeof(void*)*1, v___x_5533_);
v___x_5575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5575_, 0, v___x_5571_);
lean_ctor_set(v___x_5575_, 1, v___x_5574_);
v___x_5576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5575_);
lean_ctor_set(v___x_5576_, 1, v___x_5536_);
v___x_5577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5577_, 0, v___x_5576_);
lean_ctor_set(v___x_5577_, 1, v___x_5538_);
v___x_5578_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5579_, 0, v___x_5577_);
lean_ctor_set(v___x_5579_, 1, v___x_5578_);
v___x_5580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5580_, 0, v___x_5579_);
lean_ctor_set(v___x_5580_, 1, v___x_5527_);
v___x_5581_ = l_Bool_repr___redArg(v_proj_5516_);
v___x_5582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5529_);
lean_ctor_set(v___x_5582_, 1, v___x_5581_);
v___x_5583_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5583_, 0, v___x_5582_);
lean_ctor_set_uint8(v___x_5583_, sizeof(void*)*1, v___x_5533_);
v___x_5584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5580_);
lean_ctor_set(v___x_5584_, 1, v___x_5583_);
v___x_5585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
lean_ctor_set(v___x_5585_, 1, v___x_5536_);
v___x_5586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5585_);
lean_ctor_set(v___x_5586_, 1, v___x_5538_);
v___x_5587_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5586_);
lean_ctor_set(v___x_5588_, 1, v___x_5587_);
v___x_5589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5588_);
lean_ctor_set(v___x_5589_, 1, v___x_5527_);
v___x_5590_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5591_ = l_Bool_repr___redArg(v_decide_5517_);
v___x_5592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5592_, 0, v___x_5590_);
lean_ctor_set(v___x_5592_, 1, v___x_5591_);
v___x_5593_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5593_, 0, v___x_5592_);
lean_ctor_set_uint8(v___x_5593_, sizeof(void*)*1, v___x_5533_);
v___x_5594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5594_, 0, v___x_5589_);
lean_ctor_set(v___x_5594_, 1, v___x_5593_);
v___x_5595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5595_, 0, v___x_5594_);
lean_ctor_set(v___x_5595_, 1, v___x_5536_);
v___x_5596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5596_, 0, v___x_5595_);
lean_ctor_set(v___x_5596_, 1, v___x_5538_);
v___x_5597_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5598_, 0, v___x_5596_);
lean_ctor_set(v___x_5598_, 1, v___x_5597_);
v___x_5599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5599_, 0, v___x_5598_);
lean_ctor_set(v___x_5599_, 1, v___x_5527_);
v___x_5600_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5601_ = l_Bool_repr___redArg(v_autoUnfold_5518_);
v___x_5602_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5602_, 0, v___x_5600_);
lean_ctor_set(v___x_5602_, 1, v___x_5601_);
v___x_5603_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5603_, 0, v___x_5602_);
lean_ctor_set_uint8(v___x_5603_, sizeof(void*)*1, v___x_5533_);
v___x_5604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5599_);
lean_ctor_set(v___x_5604_, 1, v___x_5603_);
v___x_5605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
lean_ctor_set(v___x_5605_, 1, v___x_5536_);
v___x_5606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5606_, 0, v___x_5605_);
lean_ctor_set(v___x_5606_, 1, v___x_5538_);
v___x_5607_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5608_, 0, v___x_5606_);
lean_ctor_set(v___x_5608_, 1, v___x_5607_);
v___x_5609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5608_);
lean_ctor_set(v___x_5609_, 1, v___x_5527_);
v___x_5610_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5611_ = l_Bool_repr___redArg(v_failIfUnchanged_5519_);
v___x_5612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5610_);
lean_ctor_set(v___x_5612_, 1, v___x_5611_);
v___x_5613_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5613_, 0, v___x_5612_);
lean_ctor_set_uint8(v___x_5613_, sizeof(void*)*1, v___x_5533_);
v___x_5614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5614_, 0, v___x_5609_);
lean_ctor_set(v___x_5614_, 1, v___x_5613_);
v___x_5615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5614_);
lean_ctor_set(v___x_5615_, 1, v___x_5536_);
v___x_5616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5615_);
lean_ctor_set(v___x_5616_, 1, v___x_5538_);
v___x_5617_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5616_);
lean_ctor_set(v___x_5618_, 1, v___x_5617_);
v___x_5619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5618_);
lean_ctor_set(v___x_5619_, 1, v___x_5527_);
v___x_5620_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5621_ = l_Bool_repr___redArg(v_unfoldPartialApp_5520_);
v___x_5622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5620_);
lean_ctor_set(v___x_5622_, 1, v___x_5621_);
v___x_5623_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5623_, 0, v___x_5622_);
lean_ctor_set_uint8(v___x_5623_, sizeof(void*)*1, v___x_5533_);
v___x_5624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5624_, 0, v___x_5619_);
lean_ctor_set(v___x_5624_, 1, v___x_5623_);
v___x_5625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5624_);
lean_ctor_set(v___x_5625_, 1, v___x_5536_);
v___x_5626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5625_);
lean_ctor_set(v___x_5626_, 1, v___x_5538_);
v___x_5627_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_5628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5628_, 0, v___x_5626_);
lean_ctor_set(v___x_5628_, 1, v___x_5627_);
v___x_5629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5628_);
lean_ctor_set(v___x_5629_, 1, v___x_5527_);
v___x_5630_ = l_Bool_repr___redArg(v_zetaDelta_5521_);
v___x_5631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5562_);
lean_ctor_set(v___x_5631_, 1, v___x_5630_);
v___x_5632_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5632_, 0, v___x_5631_);
lean_ctor_set_uint8(v___x_5632_, sizeof(void*)*1, v___x_5533_);
v___x_5633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5629_);
lean_ctor_set(v___x_5633_, 1, v___x_5632_);
v___x_5634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5633_);
lean_ctor_set(v___x_5634_, 1, v___x_5536_);
v___x_5635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5635_, 0, v___x_5634_);
lean_ctor_set(v___x_5635_, 1, v___x_5538_);
v___x_5636_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_5637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5635_);
lean_ctor_set(v___x_5637_, 1, v___x_5636_);
v___x_5638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5637_);
lean_ctor_set(v___x_5638_, 1, v___x_5527_);
v___x_5639_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5640_ = l_Bool_repr___redArg(v_index_5522_);
v___x_5641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5639_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5642_, 0, v___x_5641_);
lean_ctor_set_uint8(v___x_5642_, sizeof(void*)*1, v___x_5533_);
v___x_5643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5638_);
lean_ctor_set(v___x_5643_, 1, v___x_5642_);
v___x_5644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5643_);
lean_ctor_set(v___x_5644_, 1, v___x_5536_);
v___x_5645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
lean_ctor_set(v___x_5645_, 1, v___x_5538_);
v___x_5646_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_5647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5645_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
v___x_5648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
lean_ctor_set(v___x_5648_, 1, v___x_5527_);
v___x_5649_ = l_Bool_repr___redArg(v_zetaUnused_5523_);
v___x_5650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5600_);
lean_ctor_set(v___x_5650_, 1, v___x_5649_);
v___x_5651_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
lean_ctor_set_uint8(v___x_5651_, sizeof(void*)*1, v___x_5533_);
v___x_5652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5648_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5652_);
lean_ctor_set(v___x_5653_, 1, v___x_5536_);
v___x_5654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5653_);
lean_ctor_set(v___x_5654_, 1, v___x_5538_);
v___x_5655_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_5656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5654_);
lean_ctor_set(v___x_5656_, 1, v___x_5655_);
v___x_5657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5656_);
lean_ctor_set(v___x_5657_, 1, v___x_5527_);
v___x_5658_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5659_ = l_Bool_repr___redArg(v_zetaHave_5524_);
v___x_5660_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5658_);
lean_ctor_set(v___x_5660_, 1, v___x_5659_);
v___x_5661_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
lean_ctor_set_uint8(v___x_5661_, sizeof(void*)*1, v___x_5533_);
v___x_5662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5657_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
v___x_5663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v___x_5536_);
v___x_5664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
lean_ctor_set(v___x_5664_, 1, v___x_5538_);
v___x_5665_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_5666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5664_);
lean_ctor_set(v___x_5666_, 1, v___x_5665_);
v___x_5667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5667_, 0, v___x_5666_);
lean_ctor_set(v___x_5667_, 1, v___x_5527_);
v___x_5668_ = l_Bool_repr___redArg(v_locals_5525_);
v___x_5669_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5590_);
lean_ctor_set(v___x_5669_, 1, v___x_5668_);
v___x_5670_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5670_, 0, v___x_5669_);
lean_ctor_set_uint8(v___x_5670_, sizeof(void*)*1, v___x_5533_);
v___x_5671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5667_);
lean_ctor_set(v___x_5671_, 1, v___x_5670_);
v___x_5672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5671_);
lean_ctor_set(v___x_5672_, 1, v___x_5536_);
v___x_5673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
lean_ctor_set(v___x_5673_, 1, v___x_5538_);
v___x_5674_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_5675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5673_);
lean_ctor_set(v___x_5675_, 1, v___x_5674_);
v___x_5676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5675_);
lean_ctor_set(v___x_5676_, 1, v___x_5527_);
v___x_5677_ = l_Bool_repr___redArg(v_instances_5526_);
v___x_5678_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5562_);
lean_ctor_set(v___x_5678_, 1, v___x_5677_);
v___x_5679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5679_, 0, v___x_5678_);
lean_ctor_set_uint8(v___x_5679_, sizeof(void*)*1, v___x_5533_);
v___x_5680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5676_);
lean_ctor_set(v___x_5680_, 1, v___x_5679_);
v___x_5681_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_5682_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_5683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5682_);
lean_ctor_set(v___x_5683_, 1, v___x_5680_);
v___x_5684_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_5685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5683_);
lean_ctor_set(v___x_5685_, 1, v___x_5684_);
v___x_5686_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5681_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5687_, 0, v___x_5686_);
lean_ctor_set_uint8(v___x_5687_, sizeof(void*)*1, v___x_5533_);
return v___x_5687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* v_x_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5688_);
lean_dec_ref(v_x_5688_);
return v_res_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* v_x_5690_, lean_object* v_prec_5691_){
_start:
{
lean_object* v___x_5692_; 
v___x_5692_ = l_Lean_Meta_instReprConfig_repr___redArg(v_x_5690_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* v_x_5693_, lean_object* v_prec_5694_){
_start:
{
lean_object* v_res_5695_; 
v_res_5695_ = l_Lean_Meta_instReprConfig_repr(v_x_5693_, v_prec_5694_);
lean_dec(v_prec_5694_);
lean_dec_ref(v_x_5693_);
return v_res_5695_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(lean_object* v_x_5703_, lean_object* v_x_5704_){
_start:
{
if (lean_obj_tag(v_x_5703_) == 0)
{
lean_object* v___x_5705_; 
v___x_5705_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__0));
return v___x_5705_;
}
else
{
lean_object* v_val_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5717_; 
v_val_5706_ = lean_ctor_get(v_x_5703_, 0);
v_isSharedCheck_5717_ = !lean_is_exclusive(v_x_5703_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5708_ = v_x_5703_;
v_isShared_5709_ = v_isSharedCheck_5717_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_val_5706_);
lean_dec(v_x_5703_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5717_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5713_; 
v___x_5710_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___closed__2));
v___x_5711_ = l_Nat_reprFast(v_val_5706_);
if (v_isShared_5709_ == 0)
{
lean_ctor_set_tag(v___x_5708_, 3);
lean_ctor_set(v___x_5708_, 0, v___x_5711_);
v___x_5713_ = v___x_5708_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5711_);
v___x_5713_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; 
v___x_5714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5710_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = l_Repr_addAppParen(v___x_5714_, v_x_5704_);
return v___x_5715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0___boxed(lean_object* v_x_5718_, lean_object* v_x_5719_){
_start:
{
lean_object* v_res_5720_; 
v_res_5720_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_x_5718_, v_x_5719_);
lean_dec(v_x_5719_);
return v_res_5720_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_5733_; lean_object* v___x_5734_; 
v___x_5733_ = lean_unsigned_to_nat(21u);
v___x_5734_ = lean_nat_to_int(v___x_5733_);
return v___x_5734_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_5741_; lean_object* v___x_5742_; 
v___x_5741_ = lean_unsigned_to_nat(11u);
v___x_5742_ = lean_nat_to_int(v___x_5741_);
return v___x_5742_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_5758_; lean_object* v___x_5759_; 
v___x_5758_ = lean_unsigned_to_nat(23u);
v___x_5759_ = lean_nat_to_int(v___x_5758_);
return v___x_5759_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5763_ = lean_unsigned_to_nat(16u);
v___x_5764_ = lean_nat_to_int(v___x_5763_);
return v___x_5764_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30(void){
_start:
{
lean_object* v___x_5771_; lean_object* v___x_5772_; 
v___x_5771_ = lean_unsigned_to_nat(15u);
v___x_5772_ = lean_nat_to_int(v___x_5771_);
return v___x_5772_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35(void){
_start:
{
lean_object* v___x_5779_; lean_object* v___x_5780_; 
v___x_5779_ = lean_unsigned_to_nat(17u);
v___x_5780_ = lean_nat_to_int(v___x_5779_);
return v___x_5780_;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40(void){
_start:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; 
v___x_5787_ = lean_unsigned_to_nat(18u);
v___x_5788_ = lean_nat_to_int(v___x_5787_);
return v___x_5788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* v_x_5789_){
_start:
{
lean_object* v_maxSteps_5790_; lean_object* v_maxDischargeDepth_5791_; uint8_t v_contextual_5792_; uint8_t v_memoize_5793_; uint8_t v_singlePass_5794_; uint8_t v_zeta_5795_; uint8_t v_beta_5796_; uint8_t v_eta_5797_; uint8_t v_etaStruct_5798_; uint8_t v_iota_5799_; uint8_t v_proj_5800_; uint8_t v_decide_5801_; uint8_t v_arith_5802_; uint8_t v_autoUnfold_5803_; uint8_t v_dsimp_5804_; uint8_t v_failIfUnchanged_5805_; uint8_t v_ground_5806_; uint8_t v_unfoldPartialApp_5807_; uint8_t v_zetaDelta_5808_; uint8_t v_index_5809_; uint8_t v_implicitDefEqProofs_5810_; uint8_t v_zetaUnused_5811_; uint8_t v_catchRuntime_5812_; uint8_t v_zetaHave_5813_; uint8_t v_letToHave_5814_; uint8_t v_congrConsts_5815_; uint8_t v_bitVecOfNat_5816_; uint8_t v_warnExponents_5817_; uint8_t v_suggestions_5818_; lean_object* v_maxSuggestions_5819_; uint8_t v_locals_5820_; uint8_t v_instances_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; uint8_t v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v_maxSteps_5790_ = lean_ctor_get(v_x_5789_, 0);
lean_inc(v_maxSteps_5790_);
v_maxDischargeDepth_5791_ = lean_ctor_get(v_x_5789_, 1);
lean_inc(v_maxDischargeDepth_5791_);
v_contextual_5792_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3);
v_memoize_5793_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 1);
v_singlePass_5794_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 2);
v_zeta_5795_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 3);
v_beta_5796_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 4);
v_eta_5797_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 5);
v_etaStruct_5798_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 6);
v_iota_5799_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 7);
v_proj_5800_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 8);
v_decide_5801_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 9);
v_arith_5802_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 10);
v_autoUnfold_5803_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 11);
v_dsimp_5804_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 12);
v_failIfUnchanged_5805_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 13);
v_ground_5806_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_5807_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 15);
v_zetaDelta_5808_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 16);
v_index_5809_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_5810_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 18);
v_zetaUnused_5811_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 19);
v_catchRuntime_5812_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 20);
v_zetaHave_5813_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 21);
v_letToHave_5814_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 22);
v_congrConsts_5815_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 23);
v_bitVecOfNat_5816_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 24);
v_warnExponents_5817_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 25);
v_suggestions_5818_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 26);
v_maxSuggestions_5819_ = lean_ctor_get(v_x_5789_, 2);
lean_inc(v_maxSuggestions_5819_);
v_locals_5820_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 27);
v_instances_5821_ = lean_ctor_get_uint8(v_x_5789_, sizeof(void*)*3 + 28);
lean_dec_ref(v_x_5789_);
v___x_5822_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5));
v___x_5823_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3));
v___x_5824_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__37, &l_Lean_Meta_instReprConfig_repr___redArg___closed__37_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
v___x_5825_ = l_Nat_reprFast(v_maxSteps_5790_);
v___x_5826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5825_);
v___x_5827_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5827_, 0, v___x_5824_);
lean_ctor_set(v___x_5827_, 1, v___x_5826_);
v___x_5828_ = 0;
v___x_5829_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5829_, 0, v___x_5827_);
lean_ctor_set_uint8(v___x_5829_, sizeof(void*)*1, v___x_5828_);
v___x_5830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5823_);
lean_ctor_set(v___x_5830_, 1, v___x_5829_);
v___x_5831_ = ((lean_object*)(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4));
v___x_5832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5830_);
lean_ctor_set(v___x_5832_, 1, v___x_5831_);
v___x_5833_ = lean_box(1);
v___x_5834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5832_);
lean_ctor_set(v___x_5834_, 1, v___x_5833_);
v___x_5835_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5));
v___x_5836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5836_, 0, v___x_5834_);
lean_ctor_set(v___x_5836_, 1, v___x_5835_);
v___x_5837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5837_, 0, v___x_5836_);
lean_ctor_set(v___x_5837_, 1, v___x_5822_);
v___x_5838_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
v___x_5839_ = l_Nat_reprFast(v_maxDischargeDepth_5791_);
v___x_5840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5840_, 0, v___x_5839_);
v___x_5841_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5841_, 0, v___x_5838_);
lean_ctor_set(v___x_5841_, 1, v___x_5840_);
v___x_5842_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5842_, 0, v___x_5841_);
lean_ctor_set_uint8(v___x_5842_, sizeof(void*)*1, v___x_5828_);
v___x_5843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5843_, 0, v___x_5837_);
lean_ctor_set(v___x_5843_, 1, v___x_5842_);
v___x_5844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5844_, 0, v___x_5843_);
lean_ctor_set(v___x_5844_, 1, v___x_5831_);
v___x_5845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5844_);
lean_ctor_set(v___x_5845_, 1, v___x_5833_);
v___x_5846_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8));
v___x_5847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5847_, 0, v___x_5845_);
lean_ctor_set(v___x_5847_, 1, v___x_5846_);
v___x_5848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5848_, 0, v___x_5847_);
lean_ctor_set(v___x_5848_, 1, v___x_5822_);
v___x_5849_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__21, &l_Lean_Meta_instReprConfig_repr___redArg___closed__21_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
v___x_5850_ = lean_unsigned_to_nat(0u);
v___x_5851_ = l_Bool_repr___redArg(v_contextual_5792_);
v___x_5852_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5852_, 0, v___x_5849_);
lean_ctor_set(v___x_5852_, 1, v___x_5851_);
v___x_5853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5853_, 0, v___x_5852_);
lean_ctor_set_uint8(v___x_5853_, sizeof(void*)*1, v___x_5828_);
v___x_5854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5848_);
lean_ctor_set(v___x_5854_, 1, v___x_5853_);
v___x_5855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5855_, 0, v___x_5854_);
lean_ctor_set(v___x_5855_, 1, v___x_5831_);
v___x_5856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5855_);
lean_ctor_set(v___x_5856_, 1, v___x_5833_);
v___x_5857_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10));
v___x_5858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5856_);
lean_ctor_set(v___x_5858_, 1, v___x_5857_);
v___x_5859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5858_);
lean_ctor_set(v___x_5859_, 1, v___x_5822_);
v___x_5860_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
v___x_5861_ = l_Bool_repr___redArg(v_memoize_5793_);
v___x_5862_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5862_, 0, v___x_5860_);
lean_ctor_set(v___x_5862_, 1, v___x_5861_);
v___x_5863_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5863_, 0, v___x_5862_);
lean_ctor_set_uint8(v___x_5863_, sizeof(void*)*1, v___x_5828_);
v___x_5864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5859_);
lean_ctor_set(v___x_5864_, 1, v___x_5863_);
v___x_5865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5864_);
lean_ctor_set(v___x_5865_, 1, v___x_5831_);
v___x_5866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5866_, 0, v___x_5865_);
lean_ctor_set(v___x_5866_, 1, v___x_5833_);
v___x_5867_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13));
v___x_5868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5866_);
lean_ctor_set(v___x_5868_, 1, v___x_5867_);
v___x_5869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5869_, 0, v___x_5868_);
lean_ctor_set(v___x_5869_, 1, v___x_5822_);
v___x_5870_ = l_Bool_repr___redArg(v_singlePass_5794_);
v___x_5871_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5871_, 0, v___x_5849_);
lean_ctor_set(v___x_5871_, 1, v___x_5870_);
v___x_5872_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5872_, 0, v___x_5871_);
lean_ctor_set_uint8(v___x_5872_, sizeof(void*)*1, v___x_5828_);
v___x_5873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5873_, 0, v___x_5869_);
lean_ctor_set(v___x_5873_, 1, v___x_5872_);
v___x_5874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5874_, 0, v___x_5873_);
lean_ctor_set(v___x_5874_, 1, v___x_5831_);
v___x_5875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
lean_ctor_set(v___x_5875_, 1, v___x_5833_);
v___x_5876_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__1));
v___x_5877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5877_, 0, v___x_5875_);
lean_ctor_set(v___x_5877_, 1, v___x_5876_);
v___x_5878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5877_);
lean_ctor_set(v___x_5878_, 1, v___x_5822_);
v___x_5879_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__4, &l_Lean_Meta_instReprConfig_repr___redArg___closed__4_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
v___x_5880_ = l_Bool_repr___redArg(v_zeta_5795_);
v___x_5881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5879_);
lean_ctor_set(v___x_5881_, 1, v___x_5880_);
v___x_5882_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5882_, 0, v___x_5881_);
lean_ctor_set_uint8(v___x_5882_, sizeof(void*)*1, v___x_5828_);
v___x_5883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5878_);
lean_ctor_set(v___x_5883_, 1, v___x_5882_);
v___x_5884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5884_, 0, v___x_5883_);
lean_ctor_set(v___x_5884_, 1, v___x_5831_);
v___x_5885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5885_, 0, v___x_5884_);
lean_ctor_set(v___x_5885_, 1, v___x_5833_);
v___x_5886_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__6));
v___x_5887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5887_, 0, v___x_5885_);
lean_ctor_set(v___x_5887_, 1, v___x_5886_);
v___x_5888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5888_, 0, v___x_5887_);
lean_ctor_set(v___x_5888_, 1, v___x_5822_);
v___x_5889_ = l_Bool_repr___redArg(v_beta_5796_);
v___x_5890_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5890_, 0, v___x_5879_);
lean_ctor_set(v___x_5890_, 1, v___x_5889_);
v___x_5891_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5891_, 0, v___x_5890_);
lean_ctor_set_uint8(v___x_5891_, sizeof(void*)*1, v___x_5828_);
v___x_5892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5888_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5892_);
lean_ctor_set(v___x_5893_, 1, v___x_5831_);
v___x_5894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5894_, 0, v___x_5893_);
lean_ctor_set(v___x_5894_, 1, v___x_5833_);
v___x_5895_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__8));
v___x_5896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5894_);
lean_ctor_set(v___x_5896_, 1, v___x_5895_);
v___x_5897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5896_);
lean_ctor_set(v___x_5897_, 1, v___x_5822_);
v___x_5898_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
v___x_5899_ = l_Bool_repr___redArg(v_eta_5797_);
v___x_5900_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5898_);
lean_ctor_set(v___x_5900_, 1, v___x_5899_);
v___x_5901_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5901_, 0, v___x_5900_);
lean_ctor_set_uint8(v___x_5901_, sizeof(void*)*1, v___x_5828_);
v___x_5902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5897_);
lean_ctor_set(v___x_5902_, 1, v___x_5901_);
v___x_5903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5902_);
lean_ctor_set(v___x_5903_, 1, v___x_5831_);
v___x_5904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5903_);
lean_ctor_set(v___x_5904_, 1, v___x_5833_);
v___x_5905_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__10));
v___x_5906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5904_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5906_);
lean_ctor_set(v___x_5907_, 1, v___x_5822_);
v___x_5908_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__11, &l_Lean_Meta_instReprConfig_repr___redArg___closed__11_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
v___x_5909_ = l_Lean_Meta_instReprEtaStructMode_repr(v_etaStruct_5798_, v___x_5850_);
v___x_5910_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5908_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5911_, 0, v___x_5910_);
lean_ctor_set_uint8(v___x_5911_, sizeof(void*)*1, v___x_5828_);
v___x_5912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5907_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5912_);
lean_ctor_set(v___x_5913_, 1, v___x_5831_);
v___x_5914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5913_);
lean_ctor_set(v___x_5914_, 1, v___x_5833_);
v___x_5915_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__13));
v___x_5916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5916_, 0, v___x_5914_);
lean_ctor_set(v___x_5916_, 1, v___x_5915_);
v___x_5917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5916_);
lean_ctor_set(v___x_5917_, 1, v___x_5822_);
v___x_5918_ = l_Bool_repr___redArg(v_iota_5799_);
v___x_5919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5879_);
lean_ctor_set(v___x_5919_, 1, v___x_5918_);
v___x_5920_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5920_, 0, v___x_5919_);
lean_ctor_set_uint8(v___x_5920_, sizeof(void*)*1, v___x_5828_);
v___x_5921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5917_);
lean_ctor_set(v___x_5921_, 1, v___x_5920_);
v___x_5922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5921_);
lean_ctor_set(v___x_5922_, 1, v___x_5831_);
v___x_5923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5922_);
lean_ctor_set(v___x_5923_, 1, v___x_5833_);
v___x_5924_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__15));
v___x_5925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5925_, 0, v___x_5923_);
lean_ctor_set(v___x_5925_, 1, v___x_5924_);
v___x_5926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5925_);
lean_ctor_set(v___x_5926_, 1, v___x_5822_);
v___x_5927_ = l_Bool_repr___redArg(v_proj_5800_);
v___x_5928_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5928_, 0, v___x_5879_);
lean_ctor_set(v___x_5928_, 1, v___x_5927_);
v___x_5929_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5929_, 0, v___x_5928_);
lean_ctor_set_uint8(v___x_5929_, sizeof(void*)*1, v___x_5828_);
v___x_5930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5926_);
lean_ctor_set(v___x_5930_, 1, v___x_5929_);
v___x_5931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
lean_ctor_set(v___x_5931_, 1, v___x_5831_);
v___x_5932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5931_);
lean_ctor_set(v___x_5932_, 1, v___x_5833_);
v___x_5933_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__17));
v___x_5934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5932_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set(v___x_5935_, 1, v___x_5822_);
v___x_5936_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__18, &l_Lean_Meta_instReprConfig_repr___redArg___closed__18_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
v___x_5937_ = l_Bool_repr___redArg(v_decide_5801_);
v___x_5938_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5936_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set_uint8(v___x_5939_, sizeof(void*)*1, v___x_5828_);
v___x_5940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5935_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5831_);
v___x_5942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5941_);
lean_ctor_set(v___x_5942_, 1, v___x_5833_);
v___x_5943_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15));
v___x_5944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5942_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5944_);
lean_ctor_set(v___x_5945_, 1, v___x_5822_);
v___x_5946_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__32, &l_Lean_Meta_instReprConfig_repr___redArg___closed__32_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
v___x_5947_ = l_Bool_repr___redArg(v_arith_5802_);
v___x_5948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5946_);
lean_ctor_set(v___x_5948_, 1, v___x_5947_);
v___x_5949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5949_, 0, v___x_5948_);
lean_ctor_set_uint8(v___x_5949_, sizeof(void*)*1, v___x_5828_);
v___x_5950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5945_);
lean_ctor_set(v___x_5950_, 1, v___x_5949_);
v___x_5951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5950_);
lean_ctor_set(v___x_5951_, 1, v___x_5831_);
v___x_5952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5951_);
lean_ctor_set(v___x_5952_, 1, v___x_5833_);
v___x_5953_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__20));
v___x_5954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5952_);
lean_ctor_set(v___x_5954_, 1, v___x_5953_);
v___x_5955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5954_);
lean_ctor_set(v___x_5955_, 1, v___x_5822_);
v___x_5956_ = l_Bool_repr___redArg(v_autoUnfold_5803_);
v___x_5957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5849_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set_uint8(v___x_5958_, sizeof(void*)*1, v___x_5828_);
v___x_5959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5955_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v___x_5960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5960_, 0, v___x_5959_);
lean_ctor_set(v___x_5960_, 1, v___x_5831_);
v___x_5961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5960_);
lean_ctor_set(v___x_5961_, 1, v___x_5833_);
v___x_5962_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17));
v___x_5963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5963_, 0, v___x_5961_);
lean_ctor_set(v___x_5963_, 1, v___x_5962_);
v___x_5964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5964_, 0, v___x_5963_);
lean_ctor_set(v___x_5964_, 1, v___x_5822_);
v___x_5965_ = l_Bool_repr___redArg(v_dsimp_5804_);
v___x_5966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5946_);
lean_ctor_set(v___x_5966_, 1, v___x_5965_);
v___x_5967_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5967_, 0, v___x_5966_);
lean_ctor_set_uint8(v___x_5967_, sizeof(void*)*1, v___x_5828_);
v___x_5968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5964_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
lean_ctor_set(v___x_5969_, 1, v___x_5831_);
v___x_5970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5969_);
lean_ctor_set(v___x_5970_, 1, v___x_5833_);
v___x_5971_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__23));
v___x_5972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5970_);
lean_ctor_set(v___x_5972_, 1, v___x_5971_);
v___x_5973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5972_);
lean_ctor_set(v___x_5973_, 1, v___x_5822_);
v___x_5974_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__24, &l_Lean_Meta_instReprConfig_repr___redArg___closed__24_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
v___x_5975_ = l_Bool_repr___redArg(v_failIfUnchanged_5805_);
v___x_5976_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5974_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v___x_5977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5977_, 0, v___x_5976_);
lean_ctor_set_uint8(v___x_5977_, sizeof(void*)*1, v___x_5828_);
v___x_5978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5973_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
v___x_5979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
lean_ctor_set(v___x_5979_, 1, v___x_5831_);
v___x_5980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5979_);
lean_ctor_set(v___x_5980_, 1, v___x_5833_);
v___x_5981_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19));
v___x_5982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5980_);
lean_ctor_set(v___x_5982_, 1, v___x_5981_);
v___x_5983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5982_);
lean_ctor_set(v___x_5983_, 1, v___x_5822_);
v___x_5984_ = l_Bool_repr___redArg(v_ground_5806_);
v___x_5985_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5936_);
lean_ctor_set(v___x_5985_, 1, v___x_5984_);
v___x_5986_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5986_, 0, v___x_5985_);
lean_ctor_set_uint8(v___x_5986_, sizeof(void*)*1, v___x_5828_);
v___x_5987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5983_);
lean_ctor_set(v___x_5987_, 1, v___x_5986_);
v___x_5988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
lean_ctor_set(v___x_5988_, 1, v___x_5831_);
v___x_5989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5988_);
lean_ctor_set(v___x_5989_, 1, v___x_5833_);
v___x_5990_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__26));
v___x_5991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5991_);
lean_ctor_set(v___x_5992_, 1, v___x_5822_);
v___x_5993_ = lean_obj_once(&l_Lean_Meta_instReprConfig_repr___redArg___closed__27, &l_Lean_Meta_instReprConfig_repr___redArg___closed__27_once, _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
v___x_5994_ = l_Bool_repr___redArg(v_unfoldPartialApp_5807_);
v___x_5995_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5993_);
lean_ctor_set(v___x_5995_, 1, v___x_5994_);
v___x_5996_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set_uint8(v___x_5996_, sizeof(void*)*1, v___x_5828_);
v___x_5997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5997_, 0, v___x_5992_);
lean_ctor_set(v___x_5997_, 1, v___x_5996_);
v___x_5998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5997_);
lean_ctor_set(v___x_5998_, 1, v___x_5831_);
v___x_5999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5998_);
lean_ctor_set(v___x_5999_, 1, v___x_5833_);
v___x_6000_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__29));
v___x_6001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6001_, 0, v___x_5999_);
lean_ctor_set(v___x_6001_, 1, v___x_6000_);
v___x_6002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6002_, 0, v___x_6001_);
lean_ctor_set(v___x_6002_, 1, v___x_5822_);
v___x_6003_ = l_Bool_repr___redArg(v_zetaDelta_5808_);
v___x_6004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6004_, 0, v___x_5908_);
lean_ctor_set(v___x_6004_, 1, v___x_6003_);
v___x_6005_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
lean_ctor_set_uint8(v___x_6005_, sizeof(void*)*1, v___x_5828_);
v___x_6006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6002_);
lean_ctor_set(v___x_6006_, 1, v___x_6005_);
v___x_6007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_5831_);
v___x_6008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6008_, 0, v___x_6007_);
lean_ctor_set(v___x_6008_, 1, v___x_5833_);
v___x_6009_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__31));
v___x_6010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6008_);
lean_ctor_set(v___x_6010_, 1, v___x_6009_);
v___x_6011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
lean_ctor_set(v___x_6011_, 1, v___x_5822_);
v___x_6012_ = l_Bool_repr___redArg(v_index_5809_);
v___x_6013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_5946_);
lean_ctor_set(v___x_6013_, 1, v___x_6012_);
v___x_6014_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
lean_ctor_set_uint8(v___x_6014_, sizeof(void*)*1, v___x_5828_);
v___x_6015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6011_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_5831_);
v___x_6017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_5833_);
v___x_6018_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21));
v___x_6019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6017_);
lean_ctor_set(v___x_6019_, 1, v___x_6018_);
v___x_6020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
lean_ctor_set(v___x_6020_, 1, v___x_5822_);
v___x_6021_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
v___x_6022_ = l_Bool_repr___redArg(v_implicitDefEqProofs_5810_);
v___x_6023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6021_);
lean_ctor_set(v___x_6023_, 1, v___x_6022_);
v___x_6024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6024_, 0, v___x_6023_);
lean_ctor_set_uint8(v___x_6024_, sizeof(void*)*1, v___x_5828_);
v___x_6025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___x_6020_);
lean_ctor_set(v___x_6025_, 1, v___x_6024_);
v___x_6026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6025_);
lean_ctor_set(v___x_6026_, 1, v___x_5831_);
v___x_6027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6026_);
lean_ctor_set(v___x_6027_, 1, v___x_5833_);
v___x_6028_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__34));
v___x_6029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6027_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6029_);
lean_ctor_set(v___x_6030_, 1, v___x_5822_);
v___x_6031_ = l_Bool_repr___redArg(v_zetaUnused_5811_);
v___x_6032_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_5849_);
lean_ctor_set(v___x_6032_, 1, v___x_6031_);
v___x_6033_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6033_, 0, v___x_6032_);
lean_ctor_set_uint8(v___x_6033_, sizeof(void*)*1, v___x_5828_);
v___x_6034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6030_);
lean_ctor_set(v___x_6034_, 1, v___x_6033_);
v___x_6035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
lean_ctor_set(v___x_6035_, 1, v___x_5831_);
v___x_6036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
lean_ctor_set(v___x_6036_, 1, v___x_5833_);
v___x_6037_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24));
v___x_6038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6036_);
lean_ctor_set(v___x_6038_, 1, v___x_6037_);
v___x_6039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6038_);
lean_ctor_set(v___x_6039_, 1, v___x_5822_);
v___x_6040_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
v___x_6041_ = l_Bool_repr___redArg(v_catchRuntime_5812_);
v___x_6042_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6040_);
lean_ctor_set(v___x_6042_, 1, v___x_6041_);
v___x_6043_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6043_, 0, v___x_6042_);
lean_ctor_set_uint8(v___x_6043_, sizeof(void*)*1, v___x_5828_);
v___x_6044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6044_, 0, v___x_6039_);
lean_ctor_set(v___x_6044_, 1, v___x_6043_);
v___x_6045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6044_);
lean_ctor_set(v___x_6045_, 1, v___x_5831_);
v___x_6046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6046_, 0, v___x_6045_);
lean_ctor_set(v___x_6046_, 1, v___x_5833_);
v___x_6047_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__36));
v___x_6048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6046_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6048_);
lean_ctor_set(v___x_6049_, 1, v___x_5822_);
v___x_6050_ = l_Bool_repr___redArg(v_zetaHave_5813_);
v___x_6051_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_5824_);
lean_ctor_set(v___x_6051_, 1, v___x_6050_);
v___x_6052_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6052_, 0, v___x_6051_);
lean_ctor_set_uint8(v___x_6052_, sizeof(void*)*1, v___x_5828_);
v___x_6053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6049_);
lean_ctor_set(v___x_6053_, 1, v___x_6052_);
v___x_6054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
lean_ctor_set(v___x_6054_, 1, v___x_5831_);
v___x_6055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set(v___x_6055_, 1, v___x_5833_);
v___x_6056_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27));
v___x_6057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6055_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
v___x_6058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6057_);
lean_ctor_set(v___x_6058_, 1, v___x_5822_);
v___x_6059_ = l_Bool_repr___redArg(v_letToHave_5814_);
v___x_6060_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_5908_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set_uint8(v___x_6061_, sizeof(void*)*1, v___x_5828_);
v___x_6062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6058_);
lean_ctor_set(v___x_6062_, 1, v___x_6061_);
v___x_6063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v___x_5831_);
v___x_6064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
lean_ctor_set(v___x_6064_, 1, v___x_5833_);
v___x_6065_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29));
v___x_6066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6064_);
lean_ctor_set(v___x_6066_, 1, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set(v___x_6067_, 1, v___x_5822_);
v___x_6068_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
v___x_6069_ = l_Bool_repr___redArg(v_congrConsts_5815_);
v___x_6070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6068_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
lean_ctor_set_uint8(v___x_6071_, sizeof(void*)*1, v___x_5828_);
v___x_6072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6067_);
lean_ctor_set(v___x_6072_, 1, v___x_6071_);
v___x_6073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
lean_ctor_set(v___x_6073_, 1, v___x_5831_);
v___x_6074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
lean_ctor_set(v___x_6074_, 1, v___x_5833_);
v___x_6075_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32));
v___x_6076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6074_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___x_6077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6076_);
lean_ctor_set(v___x_6077_, 1, v___x_5822_);
v___x_6078_ = l_Bool_repr___redArg(v_bitVecOfNat_5816_);
v___x_6079_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6068_);
lean_ctor_set(v___x_6079_, 1, v___x_6078_);
v___x_6080_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6080_, 0, v___x_6079_);
lean_ctor_set_uint8(v___x_6080_, sizeof(void*)*1, v___x_5828_);
v___x_6081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6081_, 0, v___x_6077_);
lean_ctor_set(v___x_6081_, 1, v___x_6080_);
v___x_6082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6082_, 0, v___x_6081_);
lean_ctor_set(v___x_6082_, 1, v___x_5831_);
v___x_6083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6083_, 0, v___x_6082_);
lean_ctor_set(v___x_6083_, 1, v___x_5833_);
v___x_6084_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34));
v___x_6085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6083_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
v___x_6086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
lean_ctor_set(v___x_6086_, 1, v___x_5822_);
v___x_6087_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
v___x_6088_ = l_Bool_repr___redArg(v_warnExponents_5817_);
v___x_6089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6087_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
v___x_6090_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6090_, 0, v___x_6089_);
lean_ctor_set_uint8(v___x_6090_, sizeof(void*)*1, v___x_5828_);
v___x_6091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6086_);
lean_ctor_set(v___x_6091_, 1, v___x_6090_);
v___x_6092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6091_);
lean_ctor_set(v___x_6092_, 1, v___x_5831_);
v___x_6093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6092_);
lean_ctor_set(v___x_6093_, 1, v___x_5833_);
v___x_6094_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37));
v___x_6095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6093_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v___x_6096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set(v___x_6096_, 1, v___x_5822_);
v___x_6097_ = l_Bool_repr___redArg(v_suggestions_5818_);
v___x_6098_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6068_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
v___x_6099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6099_, 0, v___x_6098_);
lean_ctor_set_uint8(v___x_6099_, sizeof(void*)*1, v___x_5828_);
v___x_6100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6096_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
v___x_6101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
lean_ctor_set(v___x_6101_, 1, v___x_5831_);
v___x_6102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_5833_);
v___x_6103_ = ((lean_object*)(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__39));
v___x_6104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6102_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
v___x_6105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
lean_ctor_set(v___x_6105_, 1, v___x_5822_);
v___x_6106_ = lean_obj_once(&l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40, &l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40_once, _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__40);
v___x_6107_ = l_Option_repr___at___00Lean_Meta_instReprConfig__1_repr_spec__0(v_maxSuggestions_5819_, v___x_5850_);
v___x_6108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6106_);
lean_ctor_set(v___x_6108_, 1, v___x_6107_);
v___x_6109_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6109_, 0, v___x_6108_);
lean_ctor_set_uint8(v___x_6109_, sizeof(void*)*1, v___x_5828_);
v___x_6110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6110_, 0, v___x_6105_);
lean_ctor_set(v___x_6110_, 1, v___x_6109_);
v___x_6111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6110_);
lean_ctor_set(v___x_6111_, 1, v___x_5831_);
v___x_6112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___x_6111_);
lean_ctor_set(v___x_6112_, 1, v___x_5833_);
v___x_6113_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__39));
v___x_6114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6112_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v___x_6115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set(v___x_6115_, 1, v___x_5822_);
v___x_6116_ = l_Bool_repr___redArg(v_locals_5820_);
v___x_6117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_5936_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v___x_6118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6118_, 0, v___x_6117_);
lean_ctor_set_uint8(v___x_6118_, sizeof(void*)*1, v___x_5828_);
v___x_6119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6115_);
lean_ctor_set(v___x_6119_, 1, v___x_6118_);
v___x_6120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set(v___x_6120_, 1, v___x_5831_);
v___x_6121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
lean_ctor_set(v___x_6121_, 1, v___x_5833_);
v___x_6122_ = ((lean_object*)(l_Lean_Meta_instReprConfig_repr___redArg___closed__41));
v___x_6123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6121_);
lean_ctor_set(v___x_6123_, 1, v___x_6122_);
v___x_6124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6123_);
lean_ctor_set(v___x_6124_, 1, v___x_5822_);
v___x_6125_ = l_Bool_repr___redArg(v_instances_5821_);
v___x_6126_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6126_, 0, v___x_5908_);
lean_ctor_set(v___x_6126_, 1, v___x_6125_);
v___x_6127_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6127_, 0, v___x_6126_);
lean_ctor_set_uint8(v___x_6127_, sizeof(void*)*1, v___x_5828_);
v___x_6128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6124_);
lean_ctor_set(v___x_6128_, 1, v___x_6127_);
v___x_6129_ = lean_obj_once(&l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10, &l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10_once, _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
v___x_6130_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11));
v___x_6131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6130_);
lean_ctor_set(v___x_6131_, 1, v___x_6128_);
v___x_6132_ = ((lean_object*)(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12));
v___x_6133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6131_);
lean_ctor_set(v___x_6133_, 1, v___x_6132_);
v___x_6134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6129_);
lean_ctor_set(v___x_6134_, 1, v___x_6133_);
v___x_6135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set_uint8(v___x_6135_, sizeof(void*)*1, v___x_5828_);
return v___x_6135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* v_x_6136_, lean_object* v_prec_6137_){
_start:
{
lean_object* v___x_6138_; 
v___x_6138_ = l_Lean_Meta_instReprConfig__1_repr___redArg(v_x_6136_);
return v___x_6138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* v_x_6139_, lean_object* v_prec_6140_){
_start:
{
lean_object* v_res_6141_; 
v_res_6141_ = l_Lean_Meta_instReprConfig__1_repr(v_x_6139_, v_prec_6140_);
lean_dec(v_prec_6140_);
return v_res_6141_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* v_a_6144_, lean_object* v_x_6145_){
_start:
{
if (lean_obj_tag(v_x_6145_) == 0)
{
uint8_t v___x_6146_; 
v___x_6146_ = 0;
return v___x_6146_;
}
else
{
lean_object* v_head_6147_; lean_object* v_tail_6148_; uint8_t v___x_6149_; 
v_head_6147_ = lean_ctor_get(v_x_6145_, 0);
v_tail_6148_ = lean_ctor_get(v_x_6145_, 1);
v___x_6149_ = lean_nat_dec_eq(v_a_6144_, v_head_6147_);
if (v___x_6149_ == 0)
{
v_x_6145_ = v_tail_6148_;
goto _start;
}
else
{
return v___x_6149_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* v_a_6151_, lean_object* v_x_6152_){
_start:
{
uint8_t v_res_6153_; lean_object* v_r_6154_; 
v_res_6153_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_a_6151_, v_x_6152_);
lean_dec(v_x_6152_);
lean_dec(v_a_6151_);
v_r_6154_ = lean_box(v_res_6153_);
return v_r_6154_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* v_x_6155_, lean_object* v_x_6156_){
_start:
{
switch(lean_obj_tag(v_x_6155_))
{
case 0:
{
uint8_t v___x_6157_; 
v___x_6157_ = 1;
return v___x_6157_;
}
case 1:
{
lean_object* v_idxs_6158_; uint8_t v___x_6159_; 
v_idxs_6158_ = lean_ctor_get(v_x_6155_, 0);
v___x_6159_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6156_, v_idxs_6158_);
return v___x_6159_;
}
default: 
{
lean_object* v_idxs_6160_; uint8_t v___x_6161_; 
v_idxs_6160_ = lean_ctor_get(v_x_6155_, 0);
v___x_6161_ = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(v_x_6156_, v_idxs_6160_);
if (v___x_6161_ == 0)
{
uint8_t v___x_6162_; 
v___x_6162_ = 1;
return v___x_6162_;
}
else
{
uint8_t v___x_6163_; 
v___x_6163_ = 0;
return v___x_6163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* v_x_6164_, lean_object* v_x_6165_){
_start:
{
uint8_t v_res_6166_; lean_object* v_r_6167_; 
v_res_6166_ = l_Lean_Meta_Occurrences_contains(v_x_6164_, v_x_6165_);
lean_dec(v_x_6165_);
lean_dec(v_x_6164_);
v_r_6167_ = lean_box(v_res_6166_);
return v_r_6167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* v_x_6168_){
_start:
{
if (lean_obj_tag(v_x_6168_) == 0)
{
uint8_t v___x_6169_; 
v___x_6169_ = 1;
return v___x_6169_;
}
else
{
uint8_t v___x_6170_; 
v___x_6170_ = 0;
return v___x_6170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* v_x_6171_){
_start:
{
uint8_t v_res_6172_; lean_object* v_r_6173_; 
v_res_6172_ = l_Lean_Meta_Occurrences_isAll(v_x_6171_);
lean_dec(v_x_6171_);
v_r_6173_ = lean_box(v_res_6172_);
return v_r_6173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t v_x_6174_){
_start:
{
switch(v_x_6174_)
{
case 0:
{
lean_object* v___x_6175_; 
v___x_6175_ = lean_unsigned_to_nat(0u);
return v___x_6175_;
}
case 1:
{
lean_object* v___x_6176_; 
v___x_6176_ = lean_unsigned_to_nat(1u);
return v___x_6176_;
}
default: 
{
lean_object* v___x_6177_; 
v___x_6177_ = lean_unsigned_to_nat(2u);
return v___x_6177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* v_x_6178_){
_start:
{
uint8_t v_x_boxed_6179_; lean_object* v_res_6180_; 
v_x_boxed_6179_ = lean_unbox(v_x_6178_);
v_res_6180_ = l_Lean_Meta_ApplyNewGoals_ctorIdx(v_x_boxed_6179_);
return v_res_6180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* v_k_6181_){
_start:
{
lean_inc(v_k_6181_);
return v_k_6181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* v_k_6182_){
_start:
{
lean_object* v_res_6183_; 
v_res_6183_ = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(v_k_6182_);
lean_dec(v_k_6182_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* v_motive_6184_, lean_object* v_ctorIdx_6185_, uint8_t v_t_6186_, lean_object* v_h_6187_, lean_object* v_k_6188_){
_start:
{
lean_inc(v_k_6188_);
return v_k_6188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* v_motive_6189_, lean_object* v_ctorIdx_6190_, lean_object* v_t_6191_, lean_object* v_h_6192_, lean_object* v_k_6193_){
_start:
{
uint8_t v_t_boxed_6194_; lean_object* v_res_6195_; 
v_t_boxed_6194_ = lean_unbox(v_t_6191_);
v_res_6195_ = l_Lean_Meta_ApplyNewGoals_ctorElim(v_motive_6189_, v_ctorIdx_6190_, v_t_boxed_6194_, v_h_6192_, v_k_6193_);
lean_dec(v_k_6193_);
lean_dec(v_ctorIdx_6190_);
return v_res_6195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* v_nonDependentFirst_6196_){
_start:
{
lean_inc(v_nonDependentFirst_6196_);
return v_nonDependentFirst_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* v_nonDependentFirst_6197_){
_start:
{
lean_object* v_res_6198_; 
v_res_6198_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(v_nonDependentFirst_6197_);
lean_dec(v_nonDependentFirst_6197_);
return v_res_6198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* v_motive_6199_, uint8_t v_t_6200_, lean_object* v_h_6201_, lean_object* v_nonDependentFirst_6202_){
_start:
{
lean_inc(v_nonDependentFirst_6202_);
return v_nonDependentFirst_6202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* v_motive_6203_, lean_object* v_t_6204_, lean_object* v_h_6205_, lean_object* v_nonDependentFirst_6206_){
_start:
{
uint8_t v_t_boxed_6207_; lean_object* v_res_6208_; 
v_t_boxed_6207_ = lean_unbox(v_t_6204_);
v_res_6208_ = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(v_motive_6203_, v_t_boxed_6207_, v_h_6205_, v_nonDependentFirst_6206_);
lean_dec(v_nonDependentFirst_6206_);
return v_res_6208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* v_nonDependentOnly_6209_){
_start:
{
lean_inc(v_nonDependentOnly_6209_);
return v_nonDependentOnly_6209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* v_nonDependentOnly_6210_){
_start:
{
lean_object* v_res_6211_; 
v_res_6211_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(v_nonDependentOnly_6210_);
lean_dec(v_nonDependentOnly_6210_);
return v_res_6211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* v_motive_6212_, uint8_t v_t_6213_, lean_object* v_h_6214_, lean_object* v_nonDependentOnly_6215_){
_start:
{
lean_inc(v_nonDependentOnly_6215_);
return v_nonDependentOnly_6215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* v_motive_6216_, lean_object* v_t_6217_, lean_object* v_h_6218_, lean_object* v_nonDependentOnly_6219_){
_start:
{
uint8_t v_t_boxed_6220_; lean_object* v_res_6221_; 
v_t_boxed_6220_ = lean_unbox(v_t_6217_);
v_res_6221_ = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(v_motive_6216_, v_t_boxed_6220_, v_h_6218_, v_nonDependentOnly_6219_);
lean_dec(v_nonDependentOnly_6219_);
return v_res_6221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* v_all_6222_){
_start:
{
lean_inc(v_all_6222_);
return v_all_6222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* v_all_6223_){
_start:
{
lean_object* v_res_6224_; 
v_res_6224_ = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(v_all_6223_);
lean_dec(v_all_6223_);
return v_res_6224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* v_motive_6225_, uint8_t v_t_6226_, lean_object* v_h_6227_, lean_object* v_all_6228_){
_start:
{
lean_inc(v_all_6228_);
return v_all_6228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* v_motive_6229_, lean_object* v_t_6230_, lean_object* v_h_6231_, lean_object* v_all_6232_){
_start:
{
uint8_t v_t_boxed_6233_; lean_object* v_res_6234_; 
v_t_boxed_6233_ = lean_unbox(v_t_6230_);
v_res_6234_ = l_Lean_Meta_ApplyNewGoals_all_elim(v_motive_6229_, v_t_boxed_6233_, v_h_6231_, v_all_6232_);
lean_dec(v_all_6232_);
return v_res_6234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* v_c_6248_){
_start:
{
lean_object* v___x_6249_; uint8_t v___x_6250_; 
v___x_6249_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
lean_inc(v_c_6248_);
v___x_6250_ = l_Lean_Syntax_isOfKind(v_c_6248_, v___x_6249_);
if (v___x_6250_ == 0)
{
lean_object* v___x_6251_; uint8_t v___x_6252_; 
v___x_6251_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
lean_inc(v_c_6248_);
v___x_6252_ = l_Lean_Syntax_isOfKind(v_c_6248_, v___x_6251_);
if (v___x_6252_ == 0)
{
lean_object* v___x_6253_; uint8_t v___x_6254_; 
v___x_6253_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__4));
lean_inc(v_c_6248_);
v___x_6254_ = l_Lean_Syntax_isOfKind(v_c_6248_, v___x_6253_);
if (v___x_6254_ == 0)
{
lean_object* v___x_6255_; 
lean_dec(v_c_6248_);
v___x_6255_ = ((lean_object*)(l_Lean_mkSepArray___closed__0));
return v___x_6255_;
}
else
{
lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; 
v___x_6256_ = lean_unsigned_to_nat(1u);
v___x_6257_ = lean_mk_empty_array_with_capacity(v___x_6256_);
v___x_6258_ = lean_array_push(v___x_6257_, v_c_6248_);
return v___x_6258_;
}
}
else
{
lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; 
v___x_6259_ = lean_unsigned_to_nat(0u);
v___x_6260_ = l_Lean_Syntax_getArg(v_c_6248_, v___x_6259_);
lean_dec(v_c_6248_);
v___x_6261_ = l_Lean_Syntax_getArgs(v___x_6260_);
lean_dec(v___x_6260_);
return v___x_6261_;
}
}
else
{
lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; uint8_t v___x_6266_; 
v___x_6262_ = l_Lean_Syntax_getArgs(v_c_6248_);
lean_dec(v_c_6248_);
v___x_6263_ = lean_unsigned_to_nat(0u);
v___x_6264_ = ((lean_object*)(l_Lean_Syntax_SepArray_ofElems___closed__0));
v___x_6265_ = lean_array_get_size(v___x_6262_);
v___x_6266_ = lean_nat_dec_lt(v___x_6263_, v___x_6265_);
if (v___x_6266_ == 0)
{
lean_dec_ref(v___x_6262_);
return v___x_6264_;
}
else
{
size_t v___x_6267_; size_t v___x_6268_; lean_object* v___x_6269_; 
v___x_6267_ = ((size_t)0ULL);
v___x_6268_ = lean_usize_of_nat(v___x_6265_);
v___x_6269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v___x_6262_, v___x_6267_, v___x_6268_, v___x_6264_);
lean_dec_ref(v___x_6262_);
return v___x_6269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* v_as_6270_, size_t v_i_6271_, size_t v_stop_6272_, lean_object* v_b_6273_){
_start:
{
uint8_t v___x_6274_; 
v___x_6274_ = lean_usize_dec_eq(v_i_6271_, v_stop_6272_);
if (v___x_6274_ == 0)
{
lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; size_t v___x_6278_; size_t v___x_6279_; 
v___x_6275_ = lean_array_uget_borrowed(v_as_6270_, v_i_6271_);
lean_inc(v___x_6275_);
v___x_6276_ = l_Lean_Parser_Tactic_getConfigItems(v___x_6275_);
v___x_6277_ = l_Array_append___redArg(v_b_6273_, v___x_6276_);
lean_dec_ref(v___x_6276_);
v___x_6278_ = ((size_t)1ULL);
v___x_6279_ = lean_usize_add(v_i_6271_, v___x_6278_);
v_i_6271_ = v___x_6279_;
v_b_6273_ = v___x_6277_;
goto _start;
}
else
{
return v_b_6273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* v_as_6281_, lean_object* v_i_6282_, lean_object* v_stop_6283_, lean_object* v_b_6284_){
_start:
{
size_t v_i_boxed_6285_; size_t v_stop_boxed_6286_; lean_object* v_res_6287_; 
v_i_boxed_6285_ = lean_unbox_usize(v_i_6282_);
lean_dec(v_i_6282_);
v_stop_boxed_6286_ = lean_unbox_usize(v_stop_6283_);
lean_dec(v_stop_6283_);
v_res_6287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(v_as_6281_, v_i_boxed_6285_, v_stop_boxed_6286_, v_b_6284_);
lean_dec_ref(v_as_6281_);
return v_res_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* v_items_6288_){
_start:
{
lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; 
v___x_6289_ = ((lean_object*)(l_Lean_Parser_Tactic_getConfigItems___closed__2));
v___x_6290_ = lean_box(2);
v___x_6291_ = ((lean_object*)(l_Lean_mkOptionalNode___closed__1));
v___x_6292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_6292_, 0, v___x_6290_);
lean_ctor_set(v___x_6292_, 1, v___x_6291_);
lean_ctor_set(v___x_6292_, 2, v_items_6288_);
v___x_6293_ = l_Lean_Syntax_node1(v___x_6290_, v___x_6289_, v___x_6292_);
return v___x_6293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* v_cfg_6294_, lean_object* v_cfg_x27_6295_){
_start:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; 
v___x_6296_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_6294_);
v___x_6297_ = l_Lean_Parser_Tactic_getConfigItems(v_cfg_x27_6295_);
v___x_6298_ = l_Array_append___redArg(v___x_6296_, v___x_6297_);
lean_dec_ref(v___x_6297_);
v___x_6299_ = l_Lean_Parser_Tactic_mkOptConfig(v___x_6298_);
return v___x_6299_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_version_major = _init_l_Lean_version_major();
lean_mark_persistent(l_Lean_version_major);
l_Lean_version_minor = _init_l_Lean_version_minor();
lean_mark_persistent(l_Lean_version_minor);
l_Lean_version_patch = _init_l_Lean_version_patch();
lean_mark_persistent(l_Lean_version_patch);
l_Lean_githash = _init_l_Lean_githash();
lean_mark_persistent(l_Lean_githash);
l_Lean_version_isRelease = _init_l_Lean_version_isRelease();
l_Lean_version_specialDesc = _init_l_Lean_version_specialDesc();
lean_mark_persistent(l_Lean_version_specialDesc);
l_Lean_versionStringCore = _init_l_Lean_versionStringCore();
lean_mark_persistent(l_Lean_versionStringCore);
l_Lean_versionString = _init_l_Lean_versionString();
lean_mark_persistent(l_Lean_versionString);
l_Lean_toolchain = _init_l_Lean_toolchain();
lean_mark_persistent(l_Lean_toolchain);
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
l_Lean_Syntax_decodeQuotedChar___boxed__const__1 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__1);
l_Lean_Syntax_decodeQuotedChar___boxed__const__2 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__2);
l_Lean_Syntax_decodeQuotedChar___boxed__const__3 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__3);
l_Lean_Syntax_decodeQuotedChar___boxed__const__4 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__4);
l_Lean_Syntax_decodeQuotedChar___boxed__const__5 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__5);
l_Lean_Syntax_decodeQuotedChar___boxed__const__6 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__6);
l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__1);
l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1___boxed__const__2);
l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Meta_Defs(builtin);
}
#ifdef __cplusplus
}
#endif

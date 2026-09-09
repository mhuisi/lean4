// Lean compiler output
// Module: Lean.Fmt.FmtM.Attribute
// Imports: public import Lean.KeyedDeclsAttribute public import Lean.Util.ShareCommon public import Lean.Fmt.FmtM.LineInfo public import Lean.Fmt.FmtM.Comments import Lean.Compiler.InitAttr import Lean.ExtraModUses import Lean.Fmt.Util.Module public import Lean.Fmt.Core.Formatter public import Lean.Elab.InfoTree.Types import Lean.Elab.InfoTree.Basic
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Fmt_headerKind;
extern lean_object* l_Lean_Fmt_cmdsKind;
extern lean_object* l_Lean_Fmt_moduleKind;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Array_insertIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_findInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "formattedLeadingRanges"};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7;
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "formattedTrailingRanges"};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10;
static const lean_string_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12;
static lean_once_cell_t l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instReprFormattedWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instReprFormattedWhitespace_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instReprFormattedWhitespace___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instReprFormattedWhitespace = (const lean_object*)&l_Lean_Fmt_instReprFormattedWhitespace___closed__0_value;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_findChoiceResolution_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedRangeKind_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedRangeKind;
static lean_once_cell_t l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0;
static lean_once_cell_t l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedBacktrackableState_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedBacktrackableState;
static lean_once_cell_t l_Lean_Fmt_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedState_default___closed__0;
static lean_once_cell_t l_Lean_Fmt_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__0 = (const lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__0_value;
static const lean_closure_object l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__1 = (const lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__0_value),((lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__2 = (const lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState = (const lean_object*)&l_Lean_Fmt_instBacktrackableBacktrackableStateState___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default = (const lean_object*)&l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedTaggedDoc = (const lean_object*)&l_Lean_Fmt_instInhabitedTaggedDoc_default___closed__0_value;
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "FmtProvider"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 236, 229, 98, 188, 250, 110, 22)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 65, 253, 3, 148, 106, 71, 75)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "FmtM"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 159, 213, 161, 201, 106, 171, 95)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Attribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 135, 163, 172, 195, 71, 93, 157)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(131, 255, 197, 156, 51, 230, 211, 19)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 200, 25, 73, 146, 5, 187, 87)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 242, 105, 235, 81, 147, 109, 184)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtProvidersExt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(150, 4, 9, 207, 82, 17, 215, 63)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
static lean_once_cell_t l_Lean_Fmt_getFmtProviders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getFmtProviders___closed__0;
static lean_once_cell_t l_Lean_Fmt_getFmtProviders___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getFmtProviders___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_getFmtProviders(lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__7;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__8_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 104, 40, 163, 160, 76, 5, 191)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(140, 38, 40, 124, 97, 131, 29, 71)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 56, 150, 150, 115, 144, 165, 34)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(163, 132, 47, 152, 194, 11, 103, 179)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 138, 188, 185, 189, 39, 135, 78)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 230, 191, 161, 252, 34, 33, 68)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmt_provider"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 19, 28, 15, 34, 20, 237, 134)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 131, .m_capacity = 131, .m_length = 130, .m_data = "Registers a function of type `Lean.Fmt.FmtProvider` that determines the formatters of the syntax node kinds it is responsible for."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CommentCollector"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 98, 240, 240, 45, 63, 154, 195)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "commentCollectorsExt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 72, 174, 54, 199, 47, 215)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
LEAN_EXPORT lean_object* l_Lean_Fmt_getCommentCollectors(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),((lean_object*)(((size_t)(650409495) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(211, 87, 224, 78, 9, 238, 137, 3)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 17, 69, 29, 94, 147, 128, 81)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 140, 124, 114, 214, 132, 191, 193)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(53, 56, 186, 132, 197, 187, 144, 52)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "comment_collector"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 41, 124, 214, 140, 65, 138, 12)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2____boxed, .m_arity = 10, .m_num_fixed = 4, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 172, .m_capacity = 172, .m_length = 171, .m_data = "Registers a function of type `Lean.Fmt.CommentCollector` that determines the syntax ranges that the comments of the syntax nodes it is responsible for are associated with."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Invalid `["};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "]` argument: Unknown syntax kind `"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "builtin_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 186, 149, 11, 110, 160, 246, 101)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 91, 59, 249, 145, 13, 225, 114)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Register an Fmt formatter for a syntax node kind."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtAttribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 227, 253, 29, 132, 51, 110, 142)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAttribute;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "StickyTermFn"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 18, 157, 57, 152, 236, 157, 39)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "stickyTermFnsExt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__14_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 174, 81, 16, 95, 89, 87, 244)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "addBuiltinStickyTermFn"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 146, .m_capacity = 146, .m_length = 145, .m_data = "Marks a function of type `Lean.Fmt.StickyTermFn` that determines whether a term propagates the stickiness of its right-hand side in applications."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "builtin_fmt_sticky_term"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 108, 12, 189, 11, 163, 111, 169)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmt_sticky_term"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 43, 182, 158, 218, 203, 52, 123)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_propagatesRhsStickiness___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_propagatesRhsStickiness___closed__0;
static lean_once_cell_t l_Lean_Fmt_propagatesRhsStickiness___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_propagatesRhsStickiness___closed__1;
LEAN_EXPORT uint8_t l_Lean_Fmt_propagatesRhsStickiness(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_propagatesRhsStickiness___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedInfixOperationAssociativity;
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqInfixOperationAssociativity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperationAssociativity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperationAssociativity___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedInfixOperationPrecs_default = (const lean_object*)&l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedInfixOperationPrecs = (const lean_object*)&l_Lean_Fmt_instInhabitedInfixOperationPrecs_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqInfixOperationPrecs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperationPrecs___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperationPrecs___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0;
static lean_once_cell_t l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1;
static lean_once_cell_t l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedInfixOperation_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedInfixOperation;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperation_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperation_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqInfixOperation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqInfixOperation_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqInfixOperation___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqInfixOperation = (const lean_object*)&l_Lean_Fmt_instBEqInfixOperation___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "builtin_infix_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 74, 181, 48, 150, 42, 120, 103)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "infix_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 144, 112, 96, 178, 9, 77, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "Register an Fmt infix operation formatter for a syntax node kind."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InfixOperation"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 213, 114, 139, 57, 44, 99, 238)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "infixFmtAttribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 47, 14, 153, 195, 148, 187, 112)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_infixFmtAttribute;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "builtin_conditional_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 131, 96, 141, 216, 83, 24, 142)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "conditional_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 10, 147, 54, 4, 250, 52, 122)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Register an Fmt conditional formatter for a syntax node kind."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ConditionalFmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 202, 187, 174, 192, 20, 94, 223)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "conditionalFmtAttribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 12, 148, 18, 60, 64, 119, 220)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_conditionalFmtAttribute;
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "builtin_quantifier_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 115, 38, 255, 188, 195, 138, 161)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "quantifier_fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 134, 102, 113, 68, 22, 10, 145)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Register an Fmt quantifier formatter for a syntax node kind."};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "QuantifierFmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 231, 199, 190, 204, 67, 157, 147)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "quantifierFmtAttribute"};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 217, 228, 48, 55, 215, 108, 194)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_quantifierFmtAttribute;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__1(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
if (lean_obj_tag(v_x_5_) == 0)
{
lean_dec(v_x_3_);
return v_x_4_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_17_; 
v_head_6_ = lean_ctor_get(v_x_5_, 0);
v_tail_7_ = lean_ctor_get(v_x_5_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v_x_5_);
if (v_isSharedCheck_17_ == 0)
{
v___x_9_ = v_x_5_;
v_isShared_10_ = v_isSharedCheck_17_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_tail_7_);
lean_inc(v_head_6_);
lean_dec(v_x_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_17_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_12_; 
lean_inc(v_x_3_);
if (v_isShared_10_ == 0)
{
lean_ctor_set_tag(v___x_9_, 5);
lean_ctor_set(v___x_9_, 1, v_x_3_);
lean_ctor_set(v___x_9_, 0, v_x_4_);
v___x_12_ = v___x_9_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_x_4_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_x_3_);
v___x_12_ = v_reuseFailAlloc_16_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = l_Lean_Syntax_instReprRange_repr___redArg(v_head_6_);
v___x_14_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v_x_4_ = v___x_14_;
v_x_5_ = v_tail_7_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2(lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_dec(v_x_18_);
return v_x_19_;
}
else
{
lean_object* v_head_21_; lean_object* v_tail_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_32_; 
v_head_21_ = lean_ctor_get(v_x_20_, 0);
v_tail_22_ = lean_ctor_get(v_x_20_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_20_);
if (v_isSharedCheck_32_ == 0)
{
v___x_24_ = v_x_20_;
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_tail_22_);
lean_inc(v_head_21_);
lean_dec(v_x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
lean_inc(v_x_18_);
if (v_isShared_25_ == 0)
{
lean_ctor_set_tag(v___x_24_, 5);
lean_ctor_set(v___x_24_, 1, v_x_18_);
lean_ctor_set(v___x_24_, 0, v_x_19_);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_x_19_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_x_18_);
v___x_27_ = v_reuseFailAlloc_31_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = l_Lean_Syntax_instReprRange_repr___redArg(v_head_21_);
v___x_29_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2_spec__3(v_x_18_, v___x_29_, v_tail_22_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0(lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_35_; 
lean_dec(v_x_34_);
v___x_35_ = lean_box(0);
return v___x_35_;
}
else
{
lean_object* v_tail_36_; 
v_tail_36_ = lean_ctor_get(v_x_33_, 1);
if (lean_obj_tag(v_tail_36_) == 0)
{
lean_object* v_head_37_; lean_object* v___x_38_; 
lean_dec(v_x_34_);
v_head_37_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_head_37_);
lean_dec_ref_known(v_x_33_, 2);
v___x_38_ = l_Lean_Syntax_instReprRange_repr___redArg(v_head_37_);
return v___x_38_;
}
else
{
lean_object* v_head_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc(v_tail_36_);
v_head_39_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_head_39_);
lean_dec_ref_known(v_x_33_, 2);
v___x_40_ = l_Lean_Syntax_instReprRange_repr___redArg(v_head_39_);
v___x_41_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0_spec__2(v_x_34_, v___x_40_, v_tail_36_);
return v___x_41_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__0));
v___x_51_ = lean_string_length(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__5);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0(lean_object* v_xs_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_array_get_size(v_xs_61_);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_nat_dec_eq(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_65_ = lean_array_to_list(v_xs_61_);
v___x_66_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__3));
v___x_67_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0_spec__0(v___x_65_, v___x_66_);
v___x_68_ = lean_obj_once(&l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__6);
v___x_69_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__7));
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_67_);
v___x_71_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__8));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_68_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = l_Std_Format_fill(v___x_73_);
return v___x_74_;
}
else
{
lean_object* v___x_75_; 
lean_dec_ref(v_xs_61_);
v___x_75_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__10));
return v___x_75_;
}
}
}
static lean_object* _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(26u);
v___x_90_ = lean_nat_to_int(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(27u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__0));
v___x_98_ = lean_string_length(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__12);
v___x_100_ = lean_nat_to_int(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg(lean_object* v_x_105_){
_start:
{
lean_object* v_formattedLeadingRanges_106_; lean_object* v_formattedTrailingRanges_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_140_; 
v_formattedLeadingRanges_106_ = lean_ctor_get(v_x_105_, 0);
v_formattedTrailingRanges_107_ = lean_ctor_get(v_x_105_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_140_ == 0)
{
v___x_109_ = v_x_105_;
v_isShared_110_ = v_isSharedCheck_140_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_formattedTrailingRanges_107_);
lean_inc(v_formattedLeadingRanges_106_);
lean_dec(v_x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_140_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_111_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__5));
v___x_112_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__6));
v___x_113_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__7);
v___x_114_ = l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0(v_formattedLeadingRanges_106_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 4);
lean_ctor_set(v___x_109_, 1, v___x_114_);
lean_ctor_set(v___x_109_, 0, v___x_113_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_114_);
v___x_116_ = v_reuseFailAlloc_139_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_112_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = ((lean_object*)(l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0___closed__2));
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_box(1);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__9));
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_111_);
v___x_127_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__10);
v___x_128_ = l_Array_repr___at___00Lean_Fmt_instReprFormattedWhitespace_repr_spec__0(v_formattedTrailingRanges_107_);
v___x_129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*1, v___x_117_);
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_126_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_obj_once(&l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13, &l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13_once, _init_l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__13);
v___x_133_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__14));
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_131_);
v___x_135_ = ((lean_object*)(l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg___closed__15));
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_132_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_117_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr(lean_object* v_x_141_, lean_object* v_prec_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Fmt_instReprFormattedWhitespace_repr___redArg(v_x_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprFormattedWhitespace_repr___boxed(lean_object* v_x_144_, lean_object* v_prec_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Fmt_instReprFormattedWhitespace_repr(v_x_144_, v_prec_145_);
lean_dec(v_prec_145_);
return v_res_146_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
if (lean_obj_tag(v_x_150_) == 0)
{
uint8_t v___x_151_; 
v___x_151_ = 1;
return v___x_151_;
}
else
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
}
else
{
if (lean_obj_tag(v_x_150_) == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v_val_155_; uint8_t v___x_156_; 
v_val_154_ = lean_ctor_get(v_x_149_, 0);
v_val_155_ = lean_ctor_get(v_x_150_, 0);
v___x_156_ = l_Lean_Syntax_instBEqRange_beq(v_val_154_, v_val_155_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0___boxed(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(v_x_157_, v_x_158_);
lean_dec(v_x_158_);
lean_dec(v_x_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_findChoiceResolution_x3f___lam__0(lean_object* v_range_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 15)
{
lean_object* v_i_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_174_; 
v_i_163_ = lean_ctor_get(v_x_162_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_162_);
if (v_isSharedCheck_174_ == 0)
{
v___x_165_ = v_x_162_;
v_isShared_166_ = v_isSharedCheck_174_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_i_163_);
lean_dec(v_x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_174_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_stx_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v_stx_167_ = lean_ctor_get(v_i_163_, 0);
lean_inc(v_stx_167_);
lean_dec_ref(v_i_163_);
v___x_168_ = 0;
v___x_169_ = l_Lean_Syntax_getRange_x3f(v_stx_167_, v___x_168_);
lean_dec(v_stx_167_);
if (v_isShared_166_ == 0)
{
lean_ctor_set_tag(v___x_165_, 1);
lean_ctor_set(v___x_165_, 0, v_range_161_);
v___x_171_ = v___x_165_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_range_161_);
v___x_171_ = v_reuseFailAlloc_173_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
uint8_t v___x_172_; 
v___x_172_ = l_Option_instBEq_beq___at___00Lean_Fmt_findChoiceResolution_x3f_spec__0(v___x_169_, v___x_171_);
lean_dec_ref(v___x_171_);
lean_dec(v___x_169_);
return v___x_172_;
}
}
}
else
{
uint8_t v___x_175_; 
lean_dec_ref(v_x_162_);
lean_dec_ref(v_range_161_);
v___x_175_ = 0;
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f___lam__0___boxed(lean_object* v_range_176_, lean_object* v_x_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Lean_Fmt_findChoiceResolution_x3f___lam__0(v_range_176_, v_x_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_findChoiceResolution_x3f(lean_object* v_infoTree_180_, lean_object* v_range_181_){
_start:
{
lean_object* v___f_182_; lean_object* v___x_183_; 
v___f_182_ = lean_alloc_closure((void*)(l_Lean_Fmt_findChoiceResolution_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_182_, 0, v_range_181_);
v___x_183_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_182_, v_infoTree_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v_val_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_194_; 
v_val_185_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_194_ == 0)
{
v___x_187_ = v___x_183_;
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_val_185_);
lean_dec(v___x_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
if (lean_obj_tag(v_val_185_) == 15)
{
lean_object* v_i_189_; lean_object* v___x_191_; 
v_i_189_ = lean_ctor_get(v_val_185_, 0);
lean_inc_ref(v_i_189_);
lean_dec_ref_known(v_val_185_, 1);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v_i_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_i_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v___x_193_; 
lean_del_object(v___x_187_);
lean_dec(v_val_185_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx(uint8_t v_x_195_){
_start:
{
switch(v_x_195_)
{
case 0:
{
lean_object* v___x_196_; 
v___x_196_ = lean_unsigned_to_nat(0u);
return v___x_196_;
}
case 1:
{
lean_object* v___x_197_; 
v___x_197_ = lean_unsigned_to_nat(1u);
return v___x_197_;
}
default: 
{
lean_object* v___x_198_; 
v___x_198_ = lean_unsigned_to_nat(2u);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorIdx___boxed(lean_object* v_x_199_){
_start:
{
uint8_t v_x_boxed_200_; lean_object* v_res_201_; 
v_x_boxed_200_ = lean_unbox(v_x_199_);
v_res_201_ = l_Lean_Fmt_RangeKind_ctorIdx(v_x_boxed_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg(lean_object* v_k_202_){
_start:
{
lean_inc(v_k_202_);
return v_k_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___redArg___boxed(lean_object* v_k_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Fmt_RangeKind_ctorElim___redArg(v_k_203_);
lean_dec(v_k_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim(lean_object* v_motive_205_, lean_object* v_ctorIdx_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
lean_inc(v_k_209_);
return v_k_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_ctorElim___boxed(lean_object* v_motive_210_, lean_object* v_ctorIdx_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_k_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lean_Fmt_RangeKind_ctorElim(v_motive_210_, v_ctorIdx_211_, v_t_boxed_215_, v_h_213_, v_k_214_);
lean_dec(v_k_214_);
lean_dec(v_ctorIdx_211_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg(lean_object* v_whitespace_217_){
_start:
{
lean_inc(v_whitespace_217_);
return v_whitespace_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___redArg___boxed(lean_object* v_whitespace_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Fmt_RangeKind_whitespace_elim___redArg(v_whitespace_218_);
lean_dec(v_whitespace_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_whitespace_223_){
_start:
{
lean_inc(v_whitespace_223_);
return v_whitespace_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_whitespace_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_whitespace_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lean_Fmt_RangeKind_whitespace_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_whitespace_227_);
lean_dec(v_whitespace_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg(lean_object* v_node_230_){
_start:
{
lean_inc(v_node_230_);
return v_node_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___redArg___boxed(lean_object* v_node_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Fmt_RangeKind_node_elim___redArg(v_node_231_);
lean_dec(v_node_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_node_236_){
_start:
{
lean_inc(v_node_236_);
return v_node_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_node_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_node_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lean_Fmt_RangeKind_node_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_node_240_);
lean_dec(v_node_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg(lean_object* v_text_243_){
_start:
{
lean_inc(v_text_243_);
return v_text_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___redArg___boxed(lean_object* v_text_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Fmt_RangeKind_text_elim___redArg(v_text_244_);
lean_dec(v_text_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_text_249_){
_start:
{
lean_inc(v_text_249_);
return v_text_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeKind_text_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_text_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_Fmt_RangeKind_text_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_text_253_);
lean_dec(v_text_253_);
return v_res_255_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedRangeKind_default(void){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedRangeKind(void){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_box(0);
v___x_259_ = lean_unsigned_to_nat(16u);
v___x_260_ = lean_mk_array(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__0);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState_default(void){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedBacktrackableState(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Fmt_instInhabitedBacktrackableState_default;
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = l_Lean_ShareCommon_objectFactory;
v___x_267_ = l_ShareCommon_mkStateImpl(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = lean_obj_once(&l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1, &l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedBacktrackableState_default___closed__1);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_obj_once(&l_Lean_Fmt_instInhabitedState_default___closed__0, &l_Lean_Fmt_instInhabitedState_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedState_default___closed__0);
v___x_271_ = l_Lean_Fmt_instInhabitedBacktrackableState_default;
v___x_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_269_);
lean_ctor_set(v___x_272_, 3, v___x_268_);
lean_ctor_set(v___x_272_, 4, v___x_268_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState_default(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Lean_Fmt_instInhabitedState_default___closed__1, &l_Lean_Fmt_instInhabitedState_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedState_default___closed__1);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedState(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Fmt_instInhabitedState_default;
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(lean_object* v_s_275_){
_start:
{
lean_object* v_toBacktrackableState_276_; 
v_toBacktrackableState_276_ = lean_ctor_get(v_s_275_, 0);
lean_inc_ref(v_toBacktrackableState_276_);
return v_toBacktrackableState_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0___boxed(lean_object* v_s_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__0(v_s_277_);
lean_dec_ref(v_s_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBacktrackableBacktrackableStateState___lam__1(lean_object* v_s_279_, lean_object* v_d_280_){
_start:
{
lean_object* v_shareCommonState_281_; lean_object* v_freshTagId_282_; lean_object* v_missingFormatters_283_; lean_object* v_partialFormatters_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_shareCommonState_281_ = lean_ctor_get(v_s_279_, 1);
v_freshTagId_282_ = lean_ctor_get(v_s_279_, 2);
v_missingFormatters_283_ = lean_ctor_get(v_s_279_, 3);
v_partialFormatters_284_ = lean_ctor_get(v_s_279_, 4);
v_isSharedCheck_291_ = !lean_is_exclusive(v_s_279_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v_s_279_, 0);
lean_dec(v_unused_292_);
v___x_286_ = v_s_279_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_partialFormatters_284_);
lean_inc(v_missingFormatters_283_);
lean_inc(v_freshTagId_282_);
lean_inc(v_shareCommonState_281_);
lean_dec(v_s_279_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_d_280_);
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_d_280_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_shareCommonState_281_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_freshTagId_282_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_missingFormatters_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_partialFormatters_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(lean_object* v_entry_304_, lean_object* v_as_305_, lean_object* v_j_306_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_array_get_size(v_as_305_);
v___x_308_ = lean_nat_dec_lt(v_j_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec(v_j_306_);
v___x_309_ = lean_box(0);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v_priority_311_; lean_object* v_priority_312_; uint8_t v___x_313_; 
v___x_310_ = lean_array_fget_borrowed(v_as_305_, v_j_306_);
v_priority_311_ = lean_ctor_get(v___x_310_, 0);
v_priority_312_ = lean_ctor_get(v_entry_304_, 0);
v___x_313_ = lean_nat_dec_lt(v_priority_311_, v_priority_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_j_306_, v___x_314_);
lean_dec(v_j_306_);
v_j_306_ = v___x_315_;
goto _start;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_j_306_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0___boxed(lean_object* v_entry_318_, lean_object* v_as_319_, lean_object* v_j_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(v_entry_318_, v_as_319_, v_j_320_);
lean_dec_ref(v_as_319_);
lean_dec_ref(v_entry_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(lean_object* v_providers_322_, lean_object* v_entry_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider_spec__0(v_entry_323_, v_providers_322_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_array_get_size(v_providers_322_);
v___x_327_ = l_Array_insertIdx_x21___redArg(v_providers_322_, v___x_326_, v_entry_323_);
return v___x_327_;
}
else
{
lean_object* v_val_328_; lean_object* v___x_329_; 
v_val_328_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v___x_325_, 1);
v___x_329_ = l_Array_insertIdx_x21___redArg(v_providers_322_, v_val_328_, v_entry_323_);
lean_dec(v_val_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_));
v___x_334_ = lean_st_mk_ref(v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2____boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object* v_priority_338_, lean_object* v_provider_339_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_341_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___x_342_ = lean_st_ref_take(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_priority_338_);
lean_ctor_set(v___x_343_, 1, v_provider_339_);
v___x_344_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v___x_342_, v___x_343_);
v___x_345_ = lean_st_ref_put(v___x_341_, v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinFmtProvider___boxed(lean_object* v_priority_347_, lean_object* v_provider_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Fmt_addBuiltinFmtProvider(v_priority_347_, v_provider_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(lean_object* v_constName_358_, lean_object* v_env_359_, lean_object* v_opts_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3));
v___x_362_ = l_Lean_Environment_evalConstCheck___redArg(v_env_359_, v_opts_360_, v___x_361_, v_constName_358_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___boxed(lean_object* v_constName_363_, lean_object* v_env_364_, lean_object* v_opts_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1(v_constName_363_, v_env_364_, v_opts_365_);
lean_dec_ref(v_opts_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(lean_object* v_e_367_){
_start:
{
if (lean_obj_tag(v_e_367_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_377_; 
v_a_369_ = lean_ctor_get(v_e_367_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_e_367_);
if (v_isSharedCheck_377_ == 0)
{
v___x_371_ = v_e_367_;
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v_e_367_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_mk_io_user_error(v_a_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 1);
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_a_378_ = lean_ctor_get(v_e_367_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_e_367_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v_e_367_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v_e_367_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 0);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg___boxed(lean_object* v_e_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v_e_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(lean_object* v_00_u03b1_389_, lean_object* v_e_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v_e_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___boxed(lean_object* v_00_u03b1_393_, lean_object* v_e_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0(v_00_u03b1_393_, v_e_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(lean_object* v_constName_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_env_400_; lean_object* v_opts_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_env_400_ = lean_ctor_get(v_a_398_, 0);
v_opts_401_ = lean_ctor_get(v_a_398_, 1);
v___x_402_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__3));
lean_inc_ref(v_env_400_);
v___x_403_ = l_Lean_Environment_evalConstCheck___redArg(v_env_400_, v_opts_401_, v___x_402_, v_constName_397_);
v___x_404_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider___boxed(lean_object* v_constName_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_constName_405_, v_a_406_);
lean_dec_ref(v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object* v_x_409_){
_start:
{
lean_object* v_fst_410_; 
v_fst_410_ = lean_ctor_get(v_x_409_, 0);
lean_inc(v_fst_410_);
return v_fst_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(v_x_411_);
lean_dec_ref(v_x_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object* v_x_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(v_x_415_);
lean_dec_ref(v_x_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object* v_x_417_, lean_object* v_s_418_){
_start:
{
lean_object* v_fst_419_; lean_object* v___x_420_; 
v_fst_419_ = lean_ctor_get(v_s_418_, 0);
lean_inc_n(v_fst_419_, 3);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v_fst_419_);
lean_ctor_set(v___x_420_, 1, v_fst_419_);
lean_ctor_set(v___x_420_, 2, v_fst_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object* v_x_421_, lean_object* v_s_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(v_x_421_, v_s_422_);
lean_dec_ref(v_s_422_);
lean_dec_ref(v_x_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_snd_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_447_; 
v_snd_426_ = lean_ctor_get(v_x_425_, 1);
lean_inc(v_snd_426_);
v_fst_427_ = lean_ctor_get(v_x_424_, 0);
v_snd_428_ = lean_ctor_get(v_x_424_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_447_ == 0)
{
v___x_430_ = v_x_424_;
v_isShared_431_ = v_isSharedCheck_447_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_inc(v_fst_427_);
lean_dec(v_x_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_447_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_fst_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_445_; 
v_fst_432_ = lean_ctor_get(v_x_425_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_425_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v_x_425_, 1);
lean_dec(v_unused_446_);
v___x_434_ = v_x_425_;
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_fst_432_);
lean_dec(v_x_425_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_priority_436_; lean_object* v___x_438_; 
v_priority_436_ = lean_ctor_get(v_snd_426_, 0);
lean_inc(v_priority_436_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_priority_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fst_432_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_priority_436_);
v___x_438_ = v_reuseFailAlloc_444_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_439_ = lean_array_push(v_fst_427_, v___x_438_);
v___x_440_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v_snd_428_, v_snd_426_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_440_);
lean_ctor_set(v___x_430_, 0, v___x_439_);
v___x_442_ = v___x_430_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object* v___x_448_, lean_object* v___x_449_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_451_ = lean_st_ref_get(v___x_448_);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_449_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(v___x_455_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v___x_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__0(lean_object* v_as_459_, size_t v_i_460_, size_t v_stop_461_, lean_object* v_b_462_, lean_object* v___y_463_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = lean_usize_dec_eq(v_i_460_, v_stop_461_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_489_; 
v___x_466_ = lean_array_uget(v_as_459_, v_i_460_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
v_snd_468_ = lean_ctor_get(v___x_466_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_489_ == 0)
{
v___x_470_ = v___x_466_;
v_isShared_471_ = v_isSharedCheck_489_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_snd_468_);
lean_inc(v_fst_467_);
lean_dec(v___x_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_489_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_fst_467_, v___y_463_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_a_473_);
lean_ctor_set(v___x_470_, 0, v_snd_468_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_snd_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_a_473_);
v___x_475_ = v_reuseFailAlloc_480_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; size_t v___x_477_; size_t v___x_478_; 
v___x_476_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertFmtProvider(v_b_462_, v___x_475_);
v___x_477_ = ((size_t)1ULL);
v___x_478_ = lean_usize_add(v_i_460_, v___x_477_);
v_i_460_ = v___x_478_;
v_b_462_ = v___x_476_;
goto _start;
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_del_object(v___x_470_);
lean_dec(v_snd_468_);
lean_dec_ref(v_b_462_);
v_a_481_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_472_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_472_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
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
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_b_462_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_stop_493_, lean_object* v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
size_t v_i_boxed_497_; size_t v_stop_boxed_498_; lean_object* v_res_499_; 
v_i_boxed_497_ = lean_unbox_usize(v_i_492_);
lean_dec(v_i_492_);
v_stop_boxed_498_ = lean_unbox_usize(v_stop_493_);
lean_dec(v_stop_493_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__0(v_as_491_, v_i_boxed_497_, v_stop_boxed_498_, v_b_494_, v___y_495_);
lean_dec_ref(v___y_495_);
lean_dec_ref(v_as_491_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__1(lean_object* v_as_500_, size_t v_i_501_, size_t v_stop_502_, lean_object* v_b_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_a_507_; lean_object* v___y_512_; uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_eq(v_i_501_, v_stop_502_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = lean_array_uget_borrowed(v_as_500_, v_i_501_);
v___x_517_ = lean_array_get_size(v___x_516_);
v___x_518_ = lean_nat_dec_lt(v___x_515_, v___x_517_);
if (v___x_518_ == 0)
{
v_a_507_ = v_b_503_;
goto v___jp_506_;
}
else
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_le(v___x_517_, v___x_517_);
if (v___x_519_ == 0)
{
if (v___x_518_ == 0)
{
v_a_507_ = v_b_503_;
goto v___jp_506_;
}
else
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((size_t)0ULL);
v___x_521_ = lean_usize_of_nat(v___x_517_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__0(v___x_516_, v___x_520_, v___x_521_, v_b_503_, v___y_504_);
v___y_512_ = v___x_522_;
goto v___jp_511_;
}
}
else
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___x_517_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__0(v___x_516_, v___x_523_, v___x_524_, v_b_503_, v___y_504_);
v___y_512_ = v___x_525_;
goto v___jp_511_;
}
}
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_b_503_);
return v___x_526_;
}
v___jp_506_:
{
size_t v___x_508_; size_t v___x_509_; 
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_501_, v___x_508_);
v_i_501_ = v___x_509_;
v_b_503_ = v_a_507_;
goto _start;
}
v___jp_511_:
{
if (lean_obj_tag(v___y_512_) == 0)
{
lean_object* v_a_513_; 
v_a_513_ = lean_ctor_get(v___y_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___y_512_, 1);
v_a_507_ = v_a_513_;
goto v___jp_506_;
}
else
{
return v___y_512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_527_, lean_object* v_i_528_, lean_object* v_stop_529_, lean_object* v_b_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
size_t v_i_boxed_533_; size_t v_stop_boxed_534_; lean_object* v_res_535_; 
v_i_boxed_533_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_stop_boxed_534_ = lean_unbox_usize(v_stop_529_);
lean_dec(v_stop_529_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__1(v_as_527_, v_i_boxed_533_, v_stop_boxed_534_, v_b_530_, v___y_531_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v_as_527_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v_as_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_a_542_; lean_object* v___y_547_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_st_ref_get(v___x_536_);
v___x_558_ = lean_array_get_size(v_as_538_);
v___x_559_ = lean_nat_dec_lt(v___x_537_, v___x_558_);
if (v___x_559_ == 0)
{
v_a_542_ = v___x_557_;
goto v___jp_541_;
}
else
{
uint8_t v___x_560_; 
v___x_560_ = lean_nat_dec_le(v___x_558_, v___x_558_);
if (v___x_560_ == 0)
{
if (v___x_559_ == 0)
{
v_a_542_ = v___x_557_;
goto v___jp_541_;
}
else
{
size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_558_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__1(v_as_538_, v___x_561_, v___x_562_, v___x_557_, v___y_539_);
v___y_547_ = v___x_563_;
goto v___jp_546_;
}
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_558_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__spec__1(v_as_538_, v___x_564_, v___x_565_, v___x_557_, v___y_539_);
v___y_547_ = v___x_566_;
goto v___jp_546_;
}
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_mk_empty_array_with_capacity(v___x_537_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v_a_542_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
v___jp_546_:
{
if (lean_obj_tag(v___y_547_) == 0)
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___y_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___y_547_, 1);
v_a_542_ = v_a_548_;
goto v___jp_541_;
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v___y_547_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___y_547_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___y_547_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___y_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v_as_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(v___x_567_, v___x_568_, v_as_569_, v___y_570_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v_as_569_);
lean_dec(v___x_568_);
lean_dec(v___x_567_);
return v_res_572_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___f_610_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___f_610_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_610_, 0, v___x_609_);
lean_closure_set(v___f_610_, 1, v___x_608_);
return v___f_610_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___f_613_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef;
v___f_613_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_613_, 0, v___x_612_);
lean_closure_set(v___f_613_, 1, v___x_611_);
return v___f_613_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_614_ = lean_box(0);
v___x_615_ = lean_box(2);
v___f_616_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_));
v___f_617_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_));
v___f_618_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_));
v___f_619_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_);
v___f_620_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_);
v___x_621_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_));
v___x_622_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___f_620_);
lean_ctor_set(v___x_622_, 2, v___f_619_);
lean_ctor_set(v___x_622_, 3, v___f_618_);
lean_ctor_set(v___x_622_, 4, v___f_617_);
lean_ctor_set(v___x_622_, 5, v___f_616_);
lean_ctor_set(v___x_622_, 6, v___x_615_);
lean_ctor_set(v___x_622_, 7, v___x_614_);
return v___x_622_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___f_623_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_));
v___x_624_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___f_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_);
v___x_628_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2____boxed(lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_();
return v_res_630_;
}
}
static lean_object* _init_l_Lean_Fmt_getFmtProviders___closed__0(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Array_instInhabited(lean_box(0));
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Fmt_getFmtProviders___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__0, &l_Lean_Fmt_getFmtProviders___closed__0_once, _init_l_Lean_Fmt_getFmtProviders___closed__0);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFmtProviders(lean_object* v_env_634_){
_start:
{
lean_object* v___x_635_; lean_object* v_toEnvExtension_636_; lean_object* v_asyncMode_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_snd_641_; 
v___x_635_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_636_ = lean_ctor_get(v___x_635_, 0);
v_asyncMode_637_ = lean_ctor_get(v_toEnvExtension_636_, 2);
v___x_638_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_639_ = lean_box(0);
v___x_640_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_638_, v___x_635_, v_env_634_, v_asyncMode_637_, v___x_639_);
v_snd_641_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_snd_641_);
lean_dec(v___x_640_);
return v_snd_641_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_642_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__0);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg(lean_object* v_env_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; lean_object* v_nextMacroScope_651_; lean_object* v_ngen_652_; lean_object* v_auxDeclNGen_653_; lean_object* v_traceState_654_; lean_object* v_messages_655_; lean_object* v_infoState_656_; lean_object* v_snapshotTasks_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_668_; 
v___x_650_ = lean_st_ref_take(v___y_648_);
v_nextMacroScope_651_ = lean_ctor_get(v___x_650_, 1);
v_ngen_652_ = lean_ctor_get(v___x_650_, 2);
v_auxDeclNGen_653_ = lean_ctor_get(v___x_650_, 3);
v_traceState_654_ = lean_ctor_get(v___x_650_, 4);
v_messages_655_ = lean_ctor_get(v___x_650_, 6);
v_infoState_656_ = lean_ctor_get(v___x_650_, 7);
v_snapshotTasks_657_ = lean_ctor_get(v___x_650_, 8);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; lean_object* v_unused_670_; 
v_unused_669_ = lean_ctor_get(v___x_650_, 5);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v___x_650_, 0);
lean_dec(v_unused_670_);
v___x_659_ = v___x_650_;
v_isShared_660_ = v_isSharedCheck_668_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snapshotTasks_657_);
lean_inc(v_infoState_656_);
lean_inc(v_messages_655_);
lean_inc(v_traceState_654_);
lean_inc(v_auxDeclNGen_653_);
lean_inc(v_ngen_652_);
lean_inc(v_nextMacroScope_651_);
lean_dec(v___x_650_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_668_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 5, v___x_661_);
lean_ctor_set(v___x_659_, 0, v_env_647_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_env_647_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_nextMacroScope_651_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_ngen_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_auxDeclNGen_653_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_traceState_654_);
lean_ctor_set(v_reuseFailAlloc_667_, 5, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_667_, 6, v_messages_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 7, v_infoState_656_);
lean_ctor_set(v_reuseFailAlloc_667_, 8, v_snapshotTasks_657_);
v___x_663_ = v_reuseFailAlloc_667_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_st_ref_put(v___y_648_, v___x_663_);
v___x_665_ = lean_box(0);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_env_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg(v_env_671_, v___y_672_);
lean_dec(v___y_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1(lean_object* v_env_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg(v_env_675_, v___y_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1(v_env_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_684_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_685_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
lean_ctor_set(v___x_690_, 2, v___x_689_);
lean_ctor_set(v___x_690_, 3, v___x_689_);
lean_ctor_set(v___x_690_, 4, v___x_688_);
lean_ctor_set(v___x_690_, 5, v___x_688_);
lean_ctor_set(v___x_690_, 6, v___x_688_);
lean_ctor_set(v___x_690_, 7, v___x_688_);
lean_ctor_set(v___x_690_, 8, v___x_688_);
lean_ctor_set(v___x_690_, 9, v___x_688_);
lean_ctor_set(v___x_690_, 10, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_unsigned_to_nat(32u);
v___x_692_ = lean_mk_empty_array_with_capacity(v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_694_ = ((size_t)5ULL);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_unsigned_to_nat(32u);
v___x_697_ = lean_mk_empty_array_with_capacity(v___x_696_);
v___x_698_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_699_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_697_);
lean_ctor_set(v___x_699_, 2, v___x_695_);
lean_ctor_set(v___x_699_, 3, v___x_695_);
lean_ctor_set_usize(v___x_699_, 4, v___x_694_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_700_ = lean_box(1);
v___x_701_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_702_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
lean_ctor_set(v___x_703_, 2, v___x_700_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; lean_object* v_toCold_709_; lean_object* v_env_710_; lean_object* v_options_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_708_ = lean_st_ref_get(v___y_706_);
v_toCold_709_ = lean_ctor_get(v___y_705_, 0);
v_env_710_ = lean_ctor_get(v___x_708_, 0);
lean_inc_ref(v_env_710_);
lean_dec(v___x_708_);
v_options_711_ = lean_ctor_get(v_toCold_709_, 2);
v___x_712_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_713_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_711_);
v___x_714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_714_, 0, v_env_710_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
lean_ctor_set(v___x_714_, 3, v_options_711_);
v___x_715_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v_msgData_704_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0(v_msgData_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_ref_726_; lean_object* v___x_727_; lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
v_ref_726_ = lean_ctor_get(v___y_723_, 2);
v___x_727_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0(v_msg_722_, v___y_723_, v___y_724_);
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
lean_inc(v_ref_726_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_ref_726_);
lean_ctor_set(v___x_732_, 1, v_a_728_);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 1);
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v_msg_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_741_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__0));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__2));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__4));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__6));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__9(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__8));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg(lean_object* v_attrName_757_, lean_object* v_declName_758_, lean_object* v_givenType_759_, lean_object* v_expectedType_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_764_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__1);
v___x_765_ = l_Lean_MessageData_ofName(v_attrName_757_);
lean_inc_ref(v___x_765_);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__3);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = 0;
v___x_770_ = l_Lean_MessageData_ofConstName(v_declName_758_, v___x_769_);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_768_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__5);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_indentExpr(v_givenType_759_);
v___x_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__7);
v___x_777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_765_);
v___x_779_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___closed__9);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_indentExpr(v_expectedType_760_);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v___x_782_, v___y_761_, v___y_762_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_attrName_784_, lean_object* v_declName_785_, lean_object* v_givenType_786_, lean_object* v_expectedType_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg(v_attrName_784_, v_declName_785_, v_givenType_786_, v_expectedType_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_toCold_797_; lean_object* v_currRecDepth_798_; lean_object* v_ref_799_; uint8_t v_diag_800_; uint8_t v_suppressElabErrors_801_; lean_object* v_ref_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_toCold_797_ = lean_ctor_get(v___y_794_, 0);
v_currRecDepth_798_ = lean_ctor_get(v___y_794_, 1);
v_ref_799_ = lean_ctor_get(v___y_794_, 2);
v_diag_800_ = lean_ctor_get_uint8(v___y_794_, sizeof(void*)*3);
v_suppressElabErrors_801_ = lean_ctor_get_uint8(v___y_794_, sizeof(void*)*3 + 1);
v_ref_802_ = l_Lean_replaceRef(v_ref_792_, v_ref_799_);
lean_inc(v_currRecDepth_798_);
lean_inc_ref(v_toCold_797_);
v___x_803_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_803_, 0, v_toCold_797_);
lean_ctor_set(v___x_803_, 1, v_currRecDepth_798_);
lean_ctor_set(v___x_803_, 2, v_ref_802_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*3, v_diag_800_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*3 + 1, v_suppressElabErrors_801_);
v___x_804_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v_msg_793_, v___x_803_, v___y_795_);
lean_dec_ref_known(v___x_803_, 3);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_805_, lean_object* v_msg_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_805_, v_msg_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v_ref_805_);
return v_res_810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_819_ = l_Lean_stringToMessageData(v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_822_ = l_Lean_stringToMessageData(v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_831_ = l_Lean_stringToMessageData(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_832_, lean_object* v_declHint_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v_env_837_; uint8_t v___x_838_; 
v___x_836_ = lean_st_ref_get(v___y_834_);
v_env_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc_ref(v_env_837_);
lean_dec(v___x_836_);
v___x_838_ = l_Lean_Name_isAnonymous(v_declHint_833_);
if (v___x_838_ == 0)
{
uint8_t v_isExporting_839_; 
v_isExporting_839_ = lean_ctor_get_uint8(v_env_837_, sizeof(void*)*8);
if (v_isExporting_839_ == 0)
{
lean_object* v___x_840_; 
lean_dec_ref(v_env_837_);
lean_dec(v_declHint_833_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v_msg_832_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; uint8_t v___x_842_; 
lean_inc_ref(v_env_837_);
v___x_841_ = l_Lean_Environment_setExporting(v_env_837_, v___x_838_);
lean_inc(v_declHint_833_);
lean_inc_ref(v___x_841_);
v___x_842_ = l_Lean_Environment_contains(v___x_841_, v_declHint_833_, v_isExporting_839_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec_ref(v___x_841_);
lean_dec_ref(v_env_837_);
lean_dec(v_declHint_833_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v_msg_832_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_c_849_; lean_object* v___x_850_; 
v___x_844_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_845_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_846_ = l_Lean_Options_empty;
v___x_847_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_847_, 0, v___x_841_);
lean_ctor_set(v___x_847_, 1, v___x_844_);
lean_ctor_set(v___x_847_, 2, v___x_845_);
lean_ctor_set(v___x_847_, 3, v___x_846_);
lean_inc(v_declHint_833_);
v___x_848_ = l_Lean_MessageData_ofConstName(v_declHint_833_, v___x_838_);
v_c_849_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_849_, 0, v___x_847_);
lean_ctor_set(v_c_849_, 1, v___x_848_);
v___x_850_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_837_, v_declHint_833_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v_env_837_);
lean_dec(v_declHint_833_);
v___x_851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v_c_849_);
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_Lean_MessageData_note(v___x_854_);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v_msg_832_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
else
{
lean_object* v_val_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_893_; 
v_val_858_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_893_ == 0)
{
v___x_860_ = v___x_850_;
v_isShared_861_ = v_isSharedCheck_893_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_val_858_);
lean_dec(v___x_850_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_893_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_mod_865_; uint8_t v___x_866_; 
v___x_862_ = lean_box(0);
v___x_863_ = l_Lean_Environment_header(v_env_837_);
lean_dec_ref(v_env_837_);
v___x_864_ = l_Lean_EnvironmentHeader_moduleNames(v___x_863_);
v_mod_865_ = lean_array_get(v___x_862_, v___x_864_, v_val_858_);
lean_dec(v_val_858_);
lean_dec_ref(v___x_864_);
v___x_866_ = l_Lean_isPrivateName(v_declHint_833_);
lean_dec(v_declHint_833_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v_c_849_);
v___x_869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_MessageData_ofName(v_mod_865_);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Lean_MessageData_note(v___x_874_);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v_msg_832_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 0);
lean_ctor_set(v___x_860_, 0, v___x_876_);
v___x_878_ = v___x_860_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_c_849_);
v___x_882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_MessageData_ofName(v_mod_865_);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_MessageData_note(v___x_887_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v_msg_832_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 0);
lean_ctor_set(v___x_860_, 0, v___x_889_);
v___x_891_ = v___x_860_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec_ref(v_env_837_);
lean_dec(v_declHint_833_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_msg_832_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_895_, lean_object* v_declHint_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_895_, v_declHint_896_, v___y_897_);
lean_dec(v___y_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_900_, lean_object* v_declHint_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_915_; 
v___x_905_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_900_, v_declHint_901_, v___y_903_);
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_915_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_910_ = l_Lean_unknownIdentifierMessageTag;
v___x_911_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v_a_906_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_916_, lean_object* v_declHint_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_916_, v_declHint_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_922_, lean_object* v_msg_923_, lean_object* v_declHint_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v_a_929_; lean_object* v___x_930_; 
v___x_928_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_923_, v_declHint_924_, v___y_925_, v___y_926_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_922_, v_a_929_, v___y_925_, v___y_926_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_931_, lean_object* v_msg_932_, lean_object* v_declHint_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_931_, v_msg_932_, v_declHint_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v_ref_931_);
return v_res_937_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__2));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object* v_ref_944_, lean_object* v_constName_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_949_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__1);
v___x_950_ = 0;
lean_inc(v_constName_945_);
v___x_951_ = l_Lean_MessageData_ofConstName(v_constName_945_, v___x_950_);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_949_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_944_, v___x_954_, v_constName_945_, v___y_946_, v___y_947_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_956_, lean_object* v_constName_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_956_, v_constName_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v_ref_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_constName_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_ref_966_; lean_object* v___x_967_; 
v_ref_966_ = lean_ctor_get(v___y_963_, 2);
v___x_967_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_966_, v_constName_962_, v___y_963_, v___y_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_constName_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2(lean_object* v_constName_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; lean_object* v_env_978_; uint8_t v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_st_ref_get(v___y_975_);
v_env_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_ref(v_env_978_);
lean_dec(v___x_977_);
v___x_979_ = 0;
lean_inc(v_constName_973_);
v___x_980_ = l_Lean_Environment_find_x3f(v_env_978_, v_constName_973_, v___x_979_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_973_, v___y_974_, v___y_975_);
return v___x_981_;
}
else
{
lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_constName_973_);
v_val_982_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_980_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v___x_980_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 0);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_val_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2___boxed(lean_object* v_constName_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2(v_constName_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_994_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg(lean_object* v_name_1004_, uint8_t v_kind_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___y_1015_; 
v___x_1009_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_1010_ = l_Lean_MessageData_ofName(v_name_1004_);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
switch(v_kind_1005_)
{
case 0:
{
lean_object* v___x_1022_; 
v___x_1022_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___y_1015_ = v___x_1022_;
goto v___jp_1014_;
}
case 1:
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__5));
v___y_1015_ = v___x_1023_;
goto v___jp_1014_;
}
default: 
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___closed__6));
v___y_1015_ = v___x_1024_;
goto v___jp_1014_;
}
}
v___jp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_inc_ref(v___y_1015_);
v___x_1016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___y_1015_);
v___x_1017_ = l_Lean_MessageData_ofFormat(v___x_1016_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1013_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v___x_1020_, v___y_1006_, v___y_1007_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_name_1025_, lean_object* v_kind_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v_kind_boxed_1030_; lean_object* v_res_1031_; 
v_kind_boxed_1030_ = lean_unbox(v_kind_1026_);
v_res_1031_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg(v_name_1025_, v_kind_boxed_1030_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v_decl_1036_, lean_object* v_stx_1037_, uint8_t v_kind_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Attribute_Builtin_getPrio(v_stx_1037_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___x_1096_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
lean_inc(v_decl_1036_);
lean_inc(v___x_1032_);
v___x_1096_ = l_Lean_ensureAttrDeclIsMeta(v___x_1032_, v_decl_1036_, v_kind_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1096_) == 0)
{
uint8_t v___x_1097_; uint8_t v___x_1098_; 
lean_dec_ref_known(v___x_1096_, 1);
v___x_1097_ = 0;
v___x_1098_ = l_Lean_instBEqAttributeKind_beq(v_kind_1038_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec(v_a_1043_);
lean_dec(v_decl_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
v___x_1099_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg(v___x_1032_, v_kind_1038_, v___y_1039_, v___y_1040_);
return v___x_1099_;
}
else
{
v___y_1077_ = v___y_1039_;
v___y_1078_ = v___y_1040_;
goto v___jp_1076_;
}
}
else
{
lean_dec(v_a_1043_);
lean_dec(v_decl_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec(v___x_1032_);
return v___x_1096_;
}
v___jp_1044_:
{
lean_object* v___x_1047_; lean_object* v_toCold_1048_; lean_object* v_env_1049_; lean_object* v_ref_1050_; lean_object* v_options_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1047_ = lean_st_ref_get(v___y_1046_);
v_toCold_1048_ = lean_ctor_get(v___y_1045_, 0);
v_env_1049_ = lean_ctor_get(v___x_1047_, 0);
lean_inc_ref(v_env_1049_);
lean_dec(v___x_1047_);
v_ref_1050_ = lean_ctor_get(v___y_1045_, 2);
v_options_1051_ = lean_ctor_get(v_toCold_1048_, 2);
lean_inc_ref(v_options_1051_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_env_1049_);
lean_ctor_set(v___x_1052_, 1, v_options_1051_);
lean_inc(v_decl_1036_);
v___x_1053_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider(v_decl_1036_, v___x_1052_);
lean_dec_ref_known(v___x_1052_, 2);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; lean_object* v_env_1056_; lean_object* v___x_1057_; lean_object* v_toEnvExtension_1058_; lean_object* v_asyncMode_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1055_ = lean_st_ref_get(v___y_1046_);
v_env_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_env_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt;
v_toEnvExtension_1058_ = lean_ctor_get(v___x_1057_, 0);
v_asyncMode_1059_ = lean_ctor_get(v_toEnvExtension_1058_, 2);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_a_1043_);
lean_ctor_set(v___x_1060_, 1, v_a_1054_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_decl_1036_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1057_, v_env_1056_, v___x_1061_, v_asyncMode_1059_, v___x_1033_);
v___x_1063_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg(v___x_1062_, v___y_1046_);
return v___x_1063_;
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1043_);
lean_dec(v_decl_1036_);
lean_dec(v___x_1033_);
v_a_1064_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1066_ = v___x_1053_;
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1053_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1068_ = lean_io_error_to_string(v_a_1064_);
v___x_1069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
v___x_1070_ = l_Lean_MessageData_ofFormat(v___x_1069_);
lean_inc(v_ref_1050_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_ref_1050_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1071_);
v___x_1073_ = v___x_1066_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
v___jp_1076_:
{
lean_object* v___x_1079_; 
lean_inc(v_decl_1036_);
v___x_1079_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2(v_decl_1036_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = l_Lean_ConstantInfo_type(v_a_1080_);
lean_dec(v_a_1080_);
v___x_1082_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__2));
v___x_1083_ = l_Lean_Name_mkStr3(v___x_1034_, v___x_1035_, v___x_1082_);
v___x_1084_ = l_Lean_Expr_isConstOf(v___x_1081_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v_a_1043_);
lean_dec(v___x_1033_);
v___x_1085_ = lean_box(0);
v___x_1086_ = l_Lean_mkConst(v___x_1083_, v___x_1085_);
v___x_1087_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg(v___x_1032_, v_decl_1036_, v___x_1081_, v___x_1086_, v___y_1077_, v___y_1078_);
return v___x_1087_;
}
else
{
lean_dec(v___x_1083_);
lean_dec_ref(v___x_1081_);
lean_dec(v___x_1032_);
v___y_1045_ = v___y_1077_;
v___y_1046_ = v___y_1078_;
goto v___jp_1044_;
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_a_1043_);
lean_dec(v_decl_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec(v___x_1032_);
v_a_1088_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1079_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1079_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_decl_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec(v___x_1032_);
v_a_1100_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1042_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1042_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2____boxed(lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v___x_1111_, lean_object* v_decl_1112_, lean_object* v_stx_1113_, lean_object* v_kind_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v_kind_boxed_1118_; lean_object* v_res_1119_; 
v_kind_boxed_1118_ = lean_unbox(v_kind_1114_);
v_res_1119_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(v___x_1108_, v___x_1109_, v___x_1110_, v___x_1111_, v_decl_1112_, v_stx_1113_, v_kind_boxed_1118_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1119_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_1122_ = l_Lean_stringToMessageData(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_1125_ = l_Lean_stringToMessageData(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(lean_object* v___x_1126_, lean_object* v_decl_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1131_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1132_ = l_Lean_MessageData_ofName(v___x_1126_);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v___x_1135_, v___y_1128_, v___y_1129_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2____boxed(lean_object* v___x_1137_, lean_object* v_decl_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(v___x_1137_, v_decl_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v_decl_1138_);
return v_res_1142_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_unsigned_to_nat(3390004911u);
v___x_1164_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_1165_ = l_Lean_Name_num___override(v___x_1164_, v___x_1163_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_1168_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1169_ = l_Lean_Name_str___override(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_1172_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1173_ = l_Lean_Name_str___override(v___x_1172_, v___x_1171_);
return v___x_1173_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_unsigned_to_nat(2u);
v___x_1175_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__12_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1176_ = l_Lean_Name_num___override(v___x_1175_, v___x_1174_);
return v___x_1176_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1188_ = 1;
v___x_1189_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__18_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_1190_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__15_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_1191_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1192_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
lean_ctor_set(v___x_1192_, 2, v___x_1189_);
lean_ctor_set_uint8(v___x_1192_, sizeof(void*)*3, v___x_1188_);
return v___x_1192_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___f_1193_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__17_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___f_1194_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__16_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_1195_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__19_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___f_1194_);
lean_ctor_set(v___x_1196_, 2, v___f_1193_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__20_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1199_ = l_Lean_registerBuiltinAttribute(v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2____boxed(lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_();
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1202_, lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v_msg_1203_, v___y_1204_, v___y_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0(v_00_u03b1_1208_, v_msg_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b1_1214_, lean_object* v_attrName_1215_, lean_object* v_declName_1216_, lean_object* v_givenType_1217_, lean_object* v_expectedType_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg(v_attrName_1215_, v_declName_1216_, v_givenType_1217_, v_expectedType_1218_, v___y_1219_, v___y_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b1_1223_, lean_object* v_attrName_1224_, lean_object* v_declName_1225_, lean_object* v_givenType_1226_, lean_object* v_expectedType_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3(v_00_u03b1_1223_, v_attrName_1224_, v_declName_1225_, v_givenType_1226_, v_expectedType_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1232_, lean_object* v_name_1233_, uint8_t v_kind_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg(v_name_1233_, v_kind_1234_, v___y_1235_, v___y_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_name_1240_, lean_object* v_kind_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v_kind_boxed_1245_; lean_object* v_res_1246_; 
v_kind_boxed_1245_ = lean_unbox(v_kind_1241_);
v_res_1246_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4(v_00_u03b1_1239_, v_name_1240_, v_kind_boxed_1245_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_00_u03b1_1247_, lean_object* v_constName_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_1248_, v___y_1249_, v___y_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_constName_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b1_1253_, v_constName_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1259_, lean_object* v_ref_1260_, lean_object* v_constName_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(v_ref_1260_, v_constName_1261_, v___y_1262_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_ref_1267_, lean_object* v_constName_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4(v_00_u03b1_1266_, v_ref_1267_, v_constName_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v_ref_1267_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1273_, lean_object* v_ref_1274_, lean_object* v_msg_1275_, lean_object* v_declHint_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(v_ref_1274_, v_msg_1275_, v_declHint_1276_, v___y_1277_, v___y_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1281_, lean_object* v_ref_1282_, lean_object* v_msg_1283_, lean_object* v_declHint_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(v_00_u03b1_1281_, v_ref_1282_, v_msg_1283_, v_declHint_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v_ref_1282_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1289_, lean_object* v_declHint_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1289_, v_declHint_1290_, v___y_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1295_, lean_object* v_declHint_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1295_, v_declHint_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1301_, lean_object* v_ref_1302_, lean_object* v_msg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1302_, v_msg_1303_, v___y_1304_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_ref_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1308_, v_ref_1309_, v_msg_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v_ref_1309_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(lean_object* v_entry_1315_, lean_object* v_as_1316_, lean_object* v_j_1317_){
_start:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = lean_array_get_size(v_as_1316_);
v___x_1319_ = lean_nat_dec_lt(v_j_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec(v_j_1317_);
v___x_1320_ = lean_box(0);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; lean_object* v_priority_1322_; lean_object* v_priority_1323_; uint8_t v___x_1324_; 
v___x_1321_ = lean_array_fget_borrowed(v_as_1316_, v_j_1317_);
v_priority_1322_ = lean_ctor_get(v___x_1321_, 0);
v_priority_1323_ = lean_ctor_get(v_entry_1315_, 0);
v___x_1324_ = lean_nat_dec_lt(v_priority_1322_, v_priority_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_unsigned_to_nat(1u);
v___x_1326_ = lean_nat_add(v_j_1317_, v___x_1325_);
lean_dec(v_j_1317_);
v_j_1317_ = v___x_1326_;
goto _start;
}
else
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_j_1317_);
return v___x_1328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0___boxed(lean_object* v_entry_1329_, lean_object* v_as_1330_, lean_object* v_j_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1329_, v_as_1330_, v_j_1331_);
lean_dec_ref(v_as_1330_);
lean_dec_ref(v_entry_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(lean_object* v_collectors_1333_, lean_object* v_entry_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector_spec__0(v_entry_1334_, v_collectors_1333_, v___x_1335_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_array_get_size(v_collectors_1333_);
v___x_1338_ = l_Array_insertIdx_x21___redArg(v_collectors_1333_, v___x_1337_, v_entry_1334_);
return v___x_1338_;
}
else
{
lean_object* v_val_1339_; lean_object* v___x_1340_; 
v_val_1339_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1340_ = l_Array_insertIdx_x21___redArg(v_collectors_1333_, v_val_1339_, v_entry_1334_);
lean_dec(v_val_1339_);
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_));
v___x_1345_ = lean_st_mk_ref(v___x_1344_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2____boxed(lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object* v_priority_1349_, lean_object* v_collector_1350_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1352_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___x_1353_ = lean_st_ref_take(v___x_1352_);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_priority_1349_);
lean_ctor_set(v___x_1354_, 1, v_collector_1350_);
v___x_1355_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v___x_1353_, v___x_1354_);
v___x_1356_ = lean_st_ref_put(v___x_1352_, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinCommentCollector___boxed(lean_object* v_priority_1358_, lean_object* v_collector_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Fmt_addBuiltinCommentCollector(v_priority_1358_, v_collector_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(lean_object* v_constName_1367_, lean_object* v_env_1368_, lean_object* v_opts_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
v___x_1371_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1368_, v_opts_1369_, v___x_1370_, v_constName_1367_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___boxed(lean_object* v_constName_1372_, lean_object* v_env_1373_, lean_object* v_opts_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1(v_constName_1372_, v_env_1373_, v_opts_1374_);
lean_dec_ref(v_opts_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(lean_object* v_constName_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_env_1379_; lean_object* v_opts_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_env_1379_ = lean_ctor_get(v_a_1377_, 0);
v_opts_1380_ = lean_ctor_get(v_a_1377_, 1);
v___x_1381_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__1));
lean_inc_ref(v_env_1379_);
v___x_1382_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1379_, v_opts_1380_, v___x_1381_, v_constName_1376_);
v___x_1383_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector___boxed(lean_object* v_constName_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_constName_1384_, v_a_1385_);
lean_dec_ref(v_a_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object* v_x_1388_){
_start:
{
lean_object* v_fst_1389_; 
v_fst_1389_ = lean_ctor_get(v_x_1388_, 0);
lean_inc(v_fst_1389_);
return v_fst_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object* v_x_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(v_x_1390_);
lean_dec_ref(v_x_1390_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object* v_x_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_box(0);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object* v_x_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(v_x_1394_);
lean_dec_ref(v_x_1394_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object* v_x_1396_, lean_object* v_s_1397_){
_start:
{
lean_object* v_fst_1398_; lean_object* v___x_1399_; 
v_fst_1398_ = lean_ctor_get(v_s_1397_, 0);
lean_inc_n(v_fst_1398_, 3);
v___x_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1399_, 0, v_fst_1398_);
lean_ctor_set(v___x_1399_, 1, v_fst_1398_);
lean_ctor_set(v___x_1399_, 2, v_fst_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object* v_x_1400_, lean_object* v_s_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(v_x_1400_, v_s_1401_);
lean_dec_ref(v_s_1401_);
lean_dec_ref(v_x_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object* v_x_1403_, lean_object* v_x_1404_){
_start:
{
lean_object* v_snd_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1426_; 
v_snd_1405_ = lean_ctor_get(v_x_1404_, 1);
lean_inc(v_snd_1405_);
v_fst_1406_ = lean_ctor_get(v_x_1403_, 0);
v_snd_1407_ = lean_ctor_get(v_x_1403_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_x_1403_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1409_ = v_x_1403_;
v_isShared_1410_ = v_isSharedCheck_1426_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_snd_1407_);
lean_inc(v_fst_1406_);
lean_dec(v_x_1403_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1426_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_fst_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1424_; 
v_fst_1411_ = lean_ctor_get(v_x_1404_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1404_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v_x_1404_, 1);
lean_dec(v_unused_1425_);
v___x_1413_ = v_x_1404_;
v_isShared_1414_ = v_isSharedCheck_1424_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_fst_1411_);
lean_dec(v_x_1404_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1424_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_priority_1415_; lean_object* v___x_1417_; 
v_priority_1415_ = lean_ctor_get(v_snd_1405_, 0);
lean_inc(v_priority_1415_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v_priority_1415_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_fst_1411_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_priority_1415_);
v___x_1417_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_array_push(v_fst_1406_, v___x_1417_);
v___x_1419_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_snd_1407_, v_snd_1405_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___x_1419_);
lean_ctor_set(v___x_1409_, 0, v___x_1418_);
v___x_1421_ = v___x_1409_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object* v___x_1427_, lean_object* v___x_1428_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1430_ = lean_st_ref_get(v___x_1427_);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1428_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v___x_1430_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object* v___x_1434_, lean_object* v___x_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(v___x_1434_, v___x_1435_);
lean_dec(v___x_1435_);
lean_dec(v___x_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__0(lean_object* v_as_1438_, size_t v_i_1439_, size_t v_stop_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_eq(v_i_1439_, v_stop_1440_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v_fst_1446_; lean_object* v_snd_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1468_; 
v___x_1445_ = lean_array_uget(v_as_1438_, v_i_1439_);
v_fst_1446_ = lean_ctor_get(v___x_1445_, 0);
v_snd_1447_ = lean_ctor_get(v___x_1445_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1449_ = v___x_1445_;
v_isShared_1450_ = v_isSharedCheck_1468_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_snd_1447_);
lean_inc(v_fst_1446_);
lean_dec(v___x_1445_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1468_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_fst_1446_, v___y_1442_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v_a_1452_);
lean_ctor_set(v___x_1449_, 0, v_snd_1447_);
v___x_1454_ = v___x_1449_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_snd_1447_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_a_1452_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; 
v___x_1455_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_insertCommentCollector(v_b_1441_, v___x_1454_);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1439_, v___x_1456_);
v_i_1439_ = v___x_1457_;
v_b_1441_ = v___x_1455_;
goto _start;
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_del_object(v___x_1449_);
lean_dec(v_snd_1447_);
lean_dec_ref(v_b_1441_);
v_a_1460_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1451_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1451_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_b_1441_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_1470_, lean_object* v_i_1471_, lean_object* v_stop_1472_, lean_object* v_b_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
size_t v_i_boxed_1476_; size_t v_stop_boxed_1477_; lean_object* v_res_1478_; 
v_i_boxed_1476_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_stop_boxed_1477_ = lean_unbox_usize(v_stop_1472_);
lean_dec(v_stop_1472_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__0(v_as_1470_, v_i_boxed_1476_, v_stop_boxed_1477_, v_b_1473_, v___y_1474_);
lean_dec_ref(v___y_1474_);
lean_dec_ref(v_as_1470_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__1(lean_object* v_as_1479_, size_t v_i_1480_, size_t v_stop_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_a_1486_; lean_object* v___y_1491_; uint8_t v___x_1493_; 
v___x_1493_ = lean_usize_dec_eq(v_i_1480_, v_stop_1481_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_array_uget_borrowed(v_as_1479_, v_i_1480_);
v___x_1496_ = lean_array_get_size(v___x_1495_);
v___x_1497_ = lean_nat_dec_lt(v___x_1494_, v___x_1496_);
if (v___x_1497_ == 0)
{
v_a_1486_ = v_b_1482_;
goto v___jp_1485_;
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_nat_dec_le(v___x_1496_, v___x_1496_);
if (v___x_1498_ == 0)
{
if (v___x_1497_ == 0)
{
v_a_1486_ = v_b_1482_;
goto v___jp_1485_;
}
else
{
size_t v___x_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = ((size_t)0ULL);
v___x_1500_ = lean_usize_of_nat(v___x_1496_);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__0(v___x_1495_, v___x_1499_, v___x_1500_, v_b_1482_, v___y_1483_);
v___y_1491_ = v___x_1501_;
goto v___jp_1490_;
}
}
else
{
size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = ((size_t)0ULL);
v___x_1503_ = lean_usize_of_nat(v___x_1496_);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__0(v___x_1495_, v___x_1502_, v___x_1503_, v_b_1482_, v___y_1483_);
v___y_1491_ = v___x_1504_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_b_1482_);
return v___x_1505_;
}
v___jp_1485_:
{
size_t v___x_1487_; size_t v___x_1488_; 
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_add(v_i_1480_, v___x_1487_);
v_i_1480_ = v___x_1488_;
v_b_1482_ = v_a_1486_;
goto _start;
}
v___jp_1490_:
{
if (lean_obj_tag(v___y_1491_) == 0)
{
lean_object* v_a_1492_; 
v_a_1492_ = lean_ctor_get(v___y_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___y_1491_, 1);
v_a_1486_ = v_a_1492_;
goto v___jp_1485_;
}
else
{
return v___y_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_1506_, lean_object* v_i_1507_, lean_object* v_stop_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
size_t v_i_boxed_1512_; size_t v_stop_boxed_1513_; lean_object* v_res_1514_; 
v_i_boxed_1512_ = lean_unbox_usize(v_i_1507_);
lean_dec(v_i_1507_);
v_stop_boxed_1513_ = lean_unbox_usize(v_stop_1508_);
lean_dec(v_stop_1508_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__1(v_as_1506_, v_i_boxed_1512_, v_stop_boxed_1513_, v_b_1509_, v___y_1510_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_as_1506_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v_as_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_a_1521_; lean_object* v___y_1526_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = lean_st_ref_get(v___x_1515_);
v___x_1537_ = lean_array_get_size(v_as_1517_);
v___x_1538_ = lean_nat_dec_lt(v___x_1516_, v___x_1537_);
if (v___x_1538_ == 0)
{
v_a_1521_ = v___x_1536_;
goto v___jp_1520_;
}
else
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_nat_dec_le(v___x_1537_, v___x_1537_);
if (v___x_1539_ == 0)
{
if (v___x_1538_ == 0)
{
v_a_1521_ = v___x_1536_;
goto v___jp_1520_;
}
else
{
size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((size_t)0ULL);
v___x_1541_ = lean_usize_of_nat(v___x_1537_);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__1(v_as_1517_, v___x_1540_, v___x_1541_, v___x_1536_, v___y_1518_);
v___y_1526_ = v___x_1542_;
goto v___jp_1525_;
}
}
else
{
size_t v___x_1543_; size_t v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = ((size_t)0ULL);
v___x_1544_ = lean_usize_of_nat(v___x_1537_);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__spec__1(v_as_1517_, v___x_1543_, v___x_1544_, v___x_1536_, v___y_1518_);
v___y_1526_ = v___x_1545_;
goto v___jp_1525_;
}
}
v___jp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_mk_empty_array_with_capacity(v___x_1516_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v_a_1521_);
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
v___jp_1525_:
{
if (lean_obj_tag(v___y_1526_) == 0)
{
lean_object* v_a_1527_; 
v_a_1527_ = lean_ctor_get(v___y_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___y_1526_, 1);
v_a_1521_ = v_a_1527_;
goto v___jp_1520_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_a_1528_ = lean_ctor_get(v___y_1526_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___y_1526_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___y_1526_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___y_1526_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object* v___x_1546_, lean_object* v___x_1547_, lean_object* v_as_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(v___x_1546_, v___x_1547_, v_as_1548_, v___y_1549_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v_as_1548_);
lean_dec(v___x_1547_);
lean_dec(v___x_1546_);
return v_res_1551_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___f_1562_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___f_1562_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_1562_, 0, v___x_1561_);
lean_closure_set(v___f_1562_, 1, v___x_1560_);
return v___f_1562_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___f_1565_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef;
v___f_1565_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_1565_, 0, v___x_1564_);
lean_closure_set(v___f_1565_, 1, v___x_1563_);
return v___f_1565_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___f_1568_; lean_object* v___f_1569_; lean_object* v___f_1570_; lean_object* v___f_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_box(2);
v___f_1568_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_));
v___f_1569_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_));
v___f_1570_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_));
v___f_1571_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_);
v___f_1572_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_);
v___x_1573_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_));
v___x_1574_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___f_1572_);
lean_ctor_set(v___x_1574_, 2, v___f_1571_);
lean_ctor_set(v___x_1574_, 3, v___f_1570_);
lean_ctor_set(v___x_1574_, 4, v___f_1569_);
lean_ctor_set(v___x_1574_, 5, v___f_1568_);
lean_ctor_set(v___x_1574_, 6, v___x_1567_);
lean_ctor_set(v___x_1574_, 7, v___x_1566_);
return v___x_1574_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___f_1575_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_));
v___x_1576_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v___f_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_);
v___x_1580_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2____boxed(lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_();
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getCommentCollectors(lean_object* v_env_1583_){
_start:
{
lean_object* v___x_1584_; lean_object* v_toEnvExtension_1585_; lean_object* v_asyncMode_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_snd_1590_; 
v___x_1584_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_1585_ = lean_ctor_get(v___x_1584_, 0);
v_asyncMode_1586_ = lean_ctor_get(v_toEnvExtension_1585_, 2);
v___x_1587_ = lean_obj_once(&l_Lean_Fmt_getFmtProviders___closed__1, &l_Lean_Fmt_getFmtProviders___closed__1_once, _init_l_Lean_Fmt_getFmtProviders___closed__1);
v___x_1588_ = lean_box(0);
v___x_1589_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1587_, v___x_1584_, v_env_1583_, v_asyncMode_1586_, v___x_1588_);
v_snd_1590_ = lean_ctor_get(v___x_1589_, 1);
lean_inc(v_snd_1590_);
lean_dec(v___x_1589_);
return v_snd_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_(lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v_decl_1595_, lean_object* v_stx_1596_, uint8_t v_kind_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Attribute_Builtin_getPrio(v_stx_1596_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___x_1655_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
lean_inc(v_decl_1595_);
lean_inc(v___x_1591_);
v___x_1655_ = l_Lean_ensureAttrDeclIsMeta(v___x_1591_, v_decl_1595_, v_kind_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1655_) == 0)
{
uint8_t v___x_1656_; uint8_t v___x_1657_; 
lean_dec_ref_known(v___x_1655_, 1);
v___x_1656_ = 0;
v___x_1657_ = l_Lean_instBEqAttributeKind_beq(v_kind_1597_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec(v_a_1602_);
lean_dec(v_decl_1595_);
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1593_);
lean_dec(v___x_1592_);
v___x_1658_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg(v___x_1591_, v_kind_1597_, v___y_1598_, v___y_1599_);
return v___x_1658_;
}
else
{
v___y_1636_ = v___y_1598_;
v___y_1637_ = v___y_1599_;
goto v___jp_1635_;
}
}
else
{
lean_dec(v_a_1602_);
lean_dec(v_decl_1595_);
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1593_);
lean_dec(v___x_1592_);
lean_dec(v___x_1591_);
return v___x_1655_;
}
v___jp_1603_:
{
lean_object* v___x_1606_; lean_object* v_toCold_1607_; lean_object* v_env_1608_; lean_object* v_ref_1609_; lean_object* v_options_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1606_ = lean_st_ref_get(v___y_1605_);
v_toCold_1607_ = lean_ctor_get(v___y_1604_, 0);
v_env_1608_ = lean_ctor_get(v___x_1606_, 0);
lean_inc_ref(v_env_1608_);
lean_dec(v___x_1606_);
v_ref_1609_ = lean_ctor_get(v___y_1604_, 2);
v_options_1610_ = lean_ctor_get(v_toCold_1607_, 2);
lean_inc_ref(v_options_1610_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_env_1608_);
lean_ctor_set(v___x_1611_, 1, v_options_1610_);
lean_inc(v_decl_1595_);
v___x_1612_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector(v_decl_1595_, v___x_1611_);
lean_dec_ref_known(v___x_1611_, 2);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; lean_object* v_env_1615_; lean_object* v___x_1616_; lean_object* v_toEnvExtension_1617_; lean_object* v_asyncMode_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = lean_st_ref_get(v___y_1605_);
v_env_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc_ref(v_env_1615_);
lean_dec(v___x_1614_);
v___x_1616_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt;
v_toEnvExtension_1617_ = lean_ctor_get(v___x_1616_, 0);
v_asyncMode_1618_ = lean_ctor_get(v_toEnvExtension_1617_, 2);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v_a_1602_);
lean_ctor_set(v___x_1619_, 1, v_a_1613_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_decl_1595_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1616_, v_env_1615_, v___x_1620_, v_asyncMode_1618_, v___x_1592_);
v___x_1622_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg(v___x_1621_, v___y_1605_);
return v___x_1622_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_a_1602_);
lean_dec(v_decl_1595_);
lean_dec(v___x_1592_);
v_a_1623_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1625_ = v___x_1612_;
v_isShared_1626_ = v_isSharedCheck_1634_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1612_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1634_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1627_ = lean_io_error_to_string(v_a_1623_);
v___x_1628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
v___x_1629_ = l_Lean_MessageData_ofFormat(v___x_1628_);
lean_inc(v_ref_1609_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_ref_1609_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1630_);
v___x_1632_ = v___x_1625_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
v___jp_1635_:
{
lean_object* v___x_1638_; 
lean_inc(v_decl_1595_);
v___x_1638_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2(v_decl_1595_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = l_Lean_ConstantInfo_type(v_a_1639_);
lean_dec(v_a_1639_);
v___x_1641_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkCommentCollector_unsafe__1___closed__0));
v___x_1642_ = l_Lean_Name_mkStr3(v___x_1593_, v___x_1594_, v___x_1641_);
v___x_1643_ = l_Lean_Expr_isConstOf(v___x_1640_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_a_1602_);
lean_dec(v___x_1592_);
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Lean_mkConst(v___x_1642_, v___x_1644_);
v___x_1646_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg(v___x_1591_, v_decl_1595_, v___x_1640_, v___x_1645_, v___y_1636_, v___y_1637_);
return v___x_1646_;
}
else
{
lean_dec(v___x_1642_);
lean_dec_ref(v___x_1640_);
lean_dec(v___x_1591_);
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___y_1637_;
goto v___jp_1603_;
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_a_1602_);
lean_dec(v_decl_1595_);
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1593_);
lean_dec(v___x_1592_);
lean_dec(v___x_1591_);
v_a_1647_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1638_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1638_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_decl_1595_);
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1593_);
lean_dec(v___x_1592_);
lean_dec(v___x_1591_);
v_a_1659_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1601_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1601_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2____boxed(lean_object* v___x_1667_, lean_object* v___x_1668_, lean_object* v___x_1669_, lean_object* v___x_1670_, lean_object* v_decl_1671_, lean_object* v_stx_1672_, lean_object* v_kind_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v_kind_boxed_1677_; lean_object* v_res_1678_; 
v_kind_boxed_1677_ = lean_unbox(v_kind_1673_);
v_res_1678_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_(v___x_1667_, v___x_1668_, v___x_1669_, v___x_1670_, v_decl_1671_, v_stx_1672_, v_kind_boxed_1677_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_(lean_object* v___x_1679_, lean_object* v_decl_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1684_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1685_ = l_Lean_MessageData_ofName(v___x_1679_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v___x_1688_, v___y_1681_, v___y_1682_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2____boxed(lean_object* v___x_1690_, lean_object* v_decl_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_(v___x_1690_, v_decl_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v_decl_1691_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_));
v___x_1730_ = l_Lean_registerBuiltinAttribute(v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2____boxed(lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_();
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg(lean_object* v_attr_1733_, lean_object* v_mk_1734_, lean_object* v_env_1735_, lean_object* v_kind_1736_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v_attr_1733_, v_env_1735_, v_kind_1736_);
v___x_1738_ = l_List_head_x3f___redArg(v___x_1737_);
lean_dec(v___x_1737_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v___x_1739_; 
lean_dec_ref(v_mk_1734_);
v___x_1739_ = lean_box(0);
return v___x_1739_;
}
else
{
lean_object* v_val_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1759_; 
v_val_1740_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1742_ = v___x_1738_;
v_isShared_1743_ = v_isSharedCheck_1759_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_val_1740_);
lean_dec(v___x_1738_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1759_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_toOLeanEntry_1744_; lean_object* v_value_1745_; lean_object* v_declName_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1757_; 
v_toOLeanEntry_1744_ = lean_ctor_get(v_val_1740_, 0);
lean_inc_ref(v_toOLeanEntry_1744_);
v_value_1745_ = lean_ctor_get(v_val_1740_, 1);
lean_inc(v_value_1745_);
lean_dec(v_val_1740_);
v_declName_1746_ = lean_ctor_get(v_toOLeanEntry_1744_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_toOLeanEntry_1744_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; 
v_unused_1758_ = lean_ctor_get(v_toOLeanEntry_1744_, 0);
lean_dec(v_unused_1758_);
v___x_1748_ = v_toOLeanEntry_1744_;
v_isShared_1749_ = v_isSharedCheck_1757_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_declName_1746_);
lean_dec(v_toOLeanEntry_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1757_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = lean_apply_1(v_mk_1734_, v_value_1745_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v___x_1750_);
lean_ctor_set(v___x_1748_, 0, v_declName_1746_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_declName_1746_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1752_);
v___x_1754_ = v___x_1742_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___redArg___boxed(lean_object* v_attr_1760_, lean_object* v_mk_1761_, lean_object* v_env_1762_, lean_object* v_kind_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_1760_, v_mk_1761_, v_env_1762_, v_kind_1763_);
lean_dec(v_kind_1763_);
lean_dec_ref(v_attr_1760_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider(lean_object* v_00_u03b1_1765_, lean_object* v_attr_1766_, lean_object* v_mk_1767_, lean_object* v_env_1768_, lean_object* v_x_1769_, lean_object* v_kind_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Fmt_keyedFmtProvider___redArg(v_attr_1766_, v_mk_1767_, v_env_1768_, v_kind_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_attr_1773_, lean_object* v_mk_1774_, lean_object* v_env_1775_, lean_object* v_x_1776_, lean_object* v_kind_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Fmt_keyedFmtProvider(v_00_u03b1_1772_, v_attr_1773_, v_mk_1774_, v_env_1775_, v_x_1776_, v_kind_1777_);
lean_dec(v_kind_1777_);
lean_dec_ref(v_x_1776_);
lean_dec_ref(v_attr_1773_);
return v_res_1778_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object* v_keys_1779_, lean_object* v_i_1780_, lean_object* v_k_1781_){
_start:
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = lean_array_get_size(v_keys_1779_);
v___x_1783_ = lean_nat_dec_lt(v_i_1780_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_dec(v_i_1780_);
return v___x_1783_;
}
else
{
lean_object* v_k_x27_1784_; uint8_t v___x_1785_; 
v_k_x27_1784_ = lean_array_fget_borrowed(v_keys_1779_, v_i_1780_);
v___x_1785_ = l_Lean_instBEqExtraModUse_beq(v_k_1781_, v_k_x27_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = lean_nat_add(v_i_1780_, v___x_1786_);
lean_dec(v_i_1780_);
v_i_1780_ = v___x_1787_;
goto _start;
}
else
{
lean_dec(v_i_1780_);
return v___x_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_keys_1789_, lean_object* v_i_1790_, lean_object* v_k_1791_){
_start:
{
uint8_t v_res_1792_; lean_object* v_r_1793_; 
v_res_1792_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_1789_, v_i_1790_, v_k_1791_);
lean_dec_ref(v_k_1791_);
lean_dec_ref(v_keys_1789_);
v_r_1793_ = lean_box(v_res_1792_);
return v_r_1793_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_1794_, size_t v_x_1795_, lean_object* v_x_1796_){
_start:
{
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v_es_1797_; lean_object* v___x_1798_; size_t v___x_1799_; size_t v___x_1800_; lean_object* v_j_1801_; lean_object* v___x_1802_; 
v_es_1797_ = lean_ctor_get(v_x_1794_, 0);
v___x_1798_ = lean_box(2);
v___x_1799_ = ((size_t)31ULL);
v___x_1800_ = lean_usize_land(v_x_1795_, v___x_1799_);
v_j_1801_ = lean_usize_to_nat(v___x_1800_);
v___x_1802_ = lean_array_get_borrowed(v___x_1798_, v_es_1797_, v_j_1801_);
lean_dec(v_j_1801_);
switch(lean_obj_tag(v___x_1802_))
{
case 0:
{
lean_object* v_key_1803_; uint8_t v___x_1804_; 
v_key_1803_ = lean_ctor_get(v___x_1802_, 0);
v___x_1804_ = l_Lean_instBEqExtraModUse_beq(v_x_1796_, v_key_1803_);
return v___x_1804_;
}
case 1:
{
lean_object* v_node_1805_; size_t v___x_1806_; size_t v___x_1807_; 
v_node_1805_ = lean_ctor_get(v___x_1802_, 0);
v___x_1806_ = ((size_t)5ULL);
v___x_1807_ = lean_usize_shift_right(v_x_1795_, v___x_1806_);
v_x_1794_ = v_node_1805_;
v_x_1795_ = v___x_1807_;
goto _start;
}
default: 
{
uint8_t v___x_1809_; 
v___x_1809_ = 0;
return v___x_1809_;
}
}
}
else
{
lean_object* v_ks_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_ks_1810_ = lean_ctor_get(v_x_1794_, 0);
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_ks_1810_, v___x_1811_, v_x_1796_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
size_t v_x_5060__boxed_1816_; uint8_t v_res_1817_; lean_object* v_r_1818_; 
v_x_5060__boxed_1816_ = lean_unbox_usize(v_x_1814_);
lean_dec(v_x_1814_);
v_res_1817_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1813_, v_x_5060__boxed_1816_, v_x_1815_);
lean_dec_ref(v_x_1815_);
lean_dec_ref(v_x_1813_);
v_r_1818_ = lean_box(v_res_1817_);
return v_r_1818_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
uint64_t v___x_1821_; size_t v___x_1822_; uint8_t v___x_1823_; 
v___x_1821_ = l_Lean_instHashableExtraModUse_hash(v_x_1820_);
v___x_1822_ = lean_uint64_to_usize(v___x_1821_);
v___x_1823_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1819_, v___x_1822_, v_x_1820_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_1824_, v_x_1825_);
lean_dec_ref(v_x_1825_);
lean_dec_ref(v_x_1824_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1828_; double v___x_1829_; 
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_float_of_nat(v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(lean_object* v_cls_1833_, lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_ref_1838_; lean_object* v___x_1839_; lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1884_; 
v_ref_1838_ = lean_ctor_get(v___y_1835_, 2);
v___x_1839_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0_spec__0(v_msg_1834_, v___y_1835_, v___y_1836_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1884_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1884_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v_traceState_1845_; lean_object* v_env_1846_; lean_object* v_nextMacroScope_1847_; lean_object* v_ngen_1848_; lean_object* v_auxDeclNGen_1849_; lean_object* v_cache_1850_; lean_object* v_messages_1851_; lean_object* v_infoState_1852_; lean_object* v_snapshotTasks_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1883_; 
v___x_1844_ = lean_st_ref_take(v___y_1836_);
v_traceState_1845_ = lean_ctor_get(v___x_1844_, 4);
v_env_1846_ = lean_ctor_get(v___x_1844_, 0);
v_nextMacroScope_1847_ = lean_ctor_get(v___x_1844_, 1);
v_ngen_1848_ = lean_ctor_get(v___x_1844_, 2);
v_auxDeclNGen_1849_ = lean_ctor_get(v___x_1844_, 3);
v_cache_1850_ = lean_ctor_get(v___x_1844_, 5);
v_messages_1851_ = lean_ctor_get(v___x_1844_, 6);
v_infoState_1852_ = lean_ctor_get(v___x_1844_, 7);
v_snapshotTasks_1853_ = lean_ctor_get(v___x_1844_, 8);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1855_ = v___x_1844_;
v_isShared_1856_ = v_isSharedCheck_1883_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_snapshotTasks_1853_);
lean_inc(v_infoState_1852_);
lean_inc(v_messages_1851_);
lean_inc(v_cache_1850_);
lean_inc(v_traceState_1845_);
lean_inc(v_auxDeclNGen_1849_);
lean_inc(v_ngen_1848_);
lean_inc(v_nextMacroScope_1847_);
lean_inc(v_env_1846_);
lean_dec(v___x_1844_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1883_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
uint64_t v_tid_1857_; lean_object* v_traces_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1882_; 
v_tid_1857_ = lean_ctor_get_uint64(v_traceState_1845_, sizeof(void*)*1);
v_traces_1858_ = lean_ctor_get(v_traceState_1845_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_traceState_1845_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1860_ = v_traceState_1845_;
v_isShared_1861_ = v_isSharedCheck_1882_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_traces_1858_);
lean_dec(v_traceState_1845_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1882_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; double v___x_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1862_ = lean_box(0);
v___x_1863_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__0);
v___x_1864_ = 0;
v___x_1865_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_1866_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1866_, 0, v_cls_1833_);
lean_ctor_set(v___x_1866_, 1, v___x_1862_);
lean_ctor_set(v___x_1866_, 2, v___x_1865_);
lean_ctor_set_float(v___x_1866_, sizeof(void*)*3, v___x_1863_);
lean_ctor_set_float(v___x_1866_, sizeof(void*)*3 + 8, v___x_1863_);
lean_ctor_set_uint8(v___x_1866_, sizeof(void*)*3 + 16, v___x_1864_);
v___x_1867_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__2));
v___x_1868_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v_a_1840_);
lean_ctor_set(v___x_1868_, 2, v___x_1867_);
lean_inc(v_ref_1838_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_ref_1838_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l_Lean_PersistentArray_push___redArg(v_traces_1858_, v___x_1869_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1870_);
v___x_1872_ = v___x_1860_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1870_);
lean_ctor_set_uint64(v_reuseFailAlloc_1881_, sizeof(void*)*1, v_tid_1857_);
v___x_1872_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1874_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 4, v___x_1872_);
v___x_1874_ = v___x_1855_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_env_1846_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_nextMacroScope_1847_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_ngen_1848_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_auxDeclNGen_1849_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1880_, 5, v_cache_1850_);
lean_ctor_set(v_reuseFailAlloc_1880_, 6, v_messages_1851_);
lean_ctor_set(v_reuseFailAlloc_1880_, 7, v_infoState_1852_);
lean_ctor_set(v_reuseFailAlloc_1880_, 8, v_snapshotTasks_1853_);
v___x_1874_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1875_ = lean_st_ref_put(v___y_1836_, v___x_1874_);
v___x_1876_ = lean_box(0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1876_);
v___x_1878_ = v___x_1842_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1885_, lean_object* v_msg_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_1885_, v_msg_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1890_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__1));
v___x_1894_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__0));
v___x_1895_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1894_, v___x_1893_);
return v___x_1895_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__5));
v___x_1901_ = l_Lean_stringToMessageData(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__7));
v___x_1904_ = l_Lean_stringToMessageData(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___x_1906_ = l_Lean_stringToMessageData(v___x_1905_);
return v___x_1906_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v_cls_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_cls_1910_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4));
v___x_1911_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__11));
v___x_1912_ = l_Lean_Name_append(v___x_1911_, v_cls_1910_);
return v___x_1912_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__13));
v___x_1915_ = l_Lean_stringToMessageData(v___x_1914_);
return v___x_1915_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__15));
v___x_1918_ = l_Lean_stringToMessageData(v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(lean_object* v_mod_1923_, uint8_t v_isMeta_1924_, lean_object* v_hint_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; lean_object* v_env_1930_; uint8_t v_isExporting_1931_; lean_object* v___x_1932_; lean_object* v_env_1933_; lean_object* v___x_1934_; lean_object* v_entry_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___y_1940_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1929_ = lean_st_ref_get(v___y_1927_);
v_env_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc_ref(v_env_1930_);
lean_dec(v___x_1929_);
v_isExporting_1931_ = lean_ctor_get_uint8(v_env_1930_, sizeof(void*)*8);
lean_dec_ref(v_env_1930_);
v___x_1932_ = lean_st_ref_get(v___y_1927_);
v_env_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc_ref(v_env_1933_);
lean_dec(v___x_1932_);
v___x_1934_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__2);
lean_inc(v_mod_1923_);
v_entry_1935_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1935_, 0, v_mod_1923_);
lean_ctor_set_uint8(v_entry_1935_, sizeof(void*)*1, v_isExporting_1931_);
lean_ctor_set_uint8(v_entry_1935_, sizeof(void*)*1 + 1, v_isMeta_1924_);
v___x_1936_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1937_ = lean_box(1);
v___x_1938_ = lean_box(0);
v___x_1965_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1934_, v___x_1936_, v_env_1933_, v___x_1937_, v___x_1938_);
v___x_1966_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v___x_1965_, v_entry_1935_);
lean_dec(v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v_toCold_1967_; lean_object* v_options_1968_; uint8_t v_hasTrace_1969_; 
v_toCold_1967_ = lean_ctor_get(v___y_1926_, 0);
v_options_1968_ = lean_ctor_get(v_toCold_1967_, 2);
v_hasTrace_1969_ = lean_ctor_get_uint8(v_options_1968_, sizeof(void*)*1);
if (v_hasTrace_1969_ == 0)
{
lean_dec(v_hint_1925_);
lean_dec(v_mod_1923_);
v___y_1940_ = v___y_1927_;
goto v___jp_1939_;
}
else
{
lean_object* v_inheritedTraceOptions_1970_; lean_object* v_cls_1971_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v_inheritedTraceOptions_1970_ = lean_ctor_get(v_toCold_1967_, 11);
v_cls_1971_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__4));
v___x_1991_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__12);
v___x_1992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1970_, v_options_1968_, v___x_1991_);
if (v___x_1992_ == 0)
{
lean_dec(v_hint_1925_);
lean_dec(v_mod_1923_);
v___y_1940_ = v___y_1927_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_1993_; lean_object* v___y_1995_; 
v___x_1993_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__14);
if (v_isExporting_1931_ == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__19));
v___y_1995_ = v___x_2002_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2003_; 
v___x_2003_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__20));
v___y_1995_ = v___x_2003_;
goto v___jp_1994_;
}
v___jp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_inc_ref(v___y_1995_);
v___x_1996_ = l_Lean_stringToMessageData(v___y_1995_);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1993_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__16);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1997_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
if (v_isMeta_1924_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__17));
v___y_1978_ = v___x_1999_;
v___y_1979_ = v___x_2000_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__18));
v___y_1978_ = v___x_1999_;
v___y_1979_ = v___x_2001_;
goto v___jp_1977_;
}
}
}
v___jp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___y_1973_);
lean_ctor_set(v___x_1975_, 1, v___y_1974_);
v___x_1976_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2(v_cls_1971_, v___x_1975_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_dec_ref_known(v___x_1976_, 1);
v___y_1940_ = v___y_1927_;
goto v___jp_1939_;
}
else
{
lean_dec_ref_known(v_entry_1935_, 1);
return v___x_1976_;
}
}
v___jp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
lean_inc_ref(v___y_1979_);
v___x_1980_ = l_Lean_stringToMessageData(v___y_1979_);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___y_1978_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__6);
v___x_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = l_Lean_MessageData_ofName(v_mod_1923_);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = l_Lean_Name_isAnonymous(v_hint_1925_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__8);
v___x_1988_ = l_Lean_MessageData_ofName(v_hint_1925_);
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___y_1973_ = v___x_1985_;
v___y_1974_ = v___x_1989_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_1990_; 
lean_dec(v_hint_1925_);
v___x_1990_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___closed__9);
v___y_1973_ = v___x_1985_;
v___y_1974_ = v___x_1990_;
goto v___jp_1972_;
}
}
}
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec_ref_known(v_entry_1935_, 1);
lean_dec(v_hint_1925_);
lean_dec(v_mod_1923_);
v___x_2004_ = lean_box(0);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
v___jp_1939_:
{
lean_object* v___x_1941_; lean_object* v_toEnvExtension_1942_; lean_object* v_env_1943_; lean_object* v_nextMacroScope_1944_; lean_object* v_ngen_1945_; lean_object* v_auxDeclNGen_1946_; lean_object* v_traceState_1947_; lean_object* v_messages_1948_; lean_object* v_infoState_1949_; lean_object* v_snapshotTasks_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1963_; 
v___x_1941_ = lean_st_ref_take(v___y_1940_);
v_toEnvExtension_1942_ = lean_ctor_get(v___x_1936_, 0);
v_env_1943_ = lean_ctor_get(v___x_1941_, 0);
v_nextMacroScope_1944_ = lean_ctor_get(v___x_1941_, 1);
v_ngen_1945_ = lean_ctor_get(v___x_1941_, 2);
v_auxDeclNGen_1946_ = lean_ctor_get(v___x_1941_, 3);
v_traceState_1947_ = lean_ctor_get(v___x_1941_, 4);
v_messages_1948_ = lean_ctor_get(v___x_1941_, 6);
v_infoState_1949_ = lean_ctor_get(v___x_1941_, 7);
v_snapshotTasks_1950_ = lean_ctor_get(v___x_1941_, 8);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v___x_1941_, 5);
lean_dec(v_unused_1964_);
v___x_1952_ = v___x_1941_;
v_isShared_1953_ = v_isSharedCheck_1963_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snapshotTasks_1950_);
lean_inc(v_infoState_1949_);
lean_inc(v_messages_1948_);
lean_inc(v_traceState_1947_);
lean_inc(v_auxDeclNGen_1946_);
lean_inc(v_ngen_1945_);
lean_inc(v_nextMacroScope_1944_);
lean_inc(v_env_1943_);
lean_dec(v___x_1941_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1963_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v_asyncMode_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v_asyncMode_1954_ = lean_ctor_get(v_toEnvExtension_1942_, 2);
v___x_1955_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1936_, v_env_1943_, v_entry_1935_, v_asyncMode_1954_, v___x_1938_);
v___x_1956_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 5, v___x_1956_);
lean_ctor_set(v___x_1952_, 0, v___x_1955_);
v___x_1958_ = v___x_1952_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_nextMacroScope_1944_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_ngen_1945_);
lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_auxDeclNGen_1946_);
lean_ctor_set(v_reuseFailAlloc_1962_, 4, v_traceState_1947_);
lean_ctor_set(v_reuseFailAlloc_1962_, 5, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1962_, 6, v_messages_1948_);
lean_ctor_set(v_reuseFailAlloc_1962_, 7, v_infoState_1949_);
lean_ctor_set(v_reuseFailAlloc_1962_, 8, v_snapshotTasks_1950_);
v___x_1958_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = lean_st_ref_put(v___y_1940_, v___x_1958_);
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0___boxed(lean_object* v_mod_2006_, lean_object* v_isMeta_2007_, lean_object* v_hint_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v_isMeta_boxed_2012_; lean_object* v_res_2013_; 
v_isMeta_boxed_2012_ = lean_unbox(v_isMeta_2007_);
v_res_2013_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_mod_2006_, v_isMeta_boxed_2012_, v_hint_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(lean_object* v___x_2014_, lean_object* v_declName_2015_, lean_object* v_as_2016_, size_t v_sz_2017_, size_t v_i_2018_, lean_object* v_b_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_usize_dec_lt(v_i_2018_, v_sz_2017_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec(v_declName_2015_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_b_2019_);
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; lean_object* v_modules_2026_; lean_object* v___x_2027_; lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v_toImport_2030_; lean_object* v_module_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2025_ = l_Lean_Environment_header(v___x_2014_);
v_modules_2026_ = lean_ctor_get(v___x_2025_, 3);
lean_inc_ref(v_modules_2026_);
lean_dec_ref(v___x_2025_);
v___x_2027_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2028_ = lean_array_uget_borrowed(v_as_2016_, v_i_2018_);
v___x_2029_ = lean_array_get(v___x_2027_, v_modules_2026_, v_a_2028_);
lean_dec_ref(v_modules_2026_);
v_toImport_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc_ref(v_toImport_2030_);
lean_dec(v___x_2029_);
v_module_2031_ = lean_ctor_get(v_toImport_2030_, 0);
lean_inc(v_module_2031_);
lean_dec_ref(v_toImport_2030_);
v___x_2032_ = 0;
lean_inc(v_declName_2015_);
v___x_2033_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2031_, v___x_2032_, v_declName_2015_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; 
lean_dec_ref_known(v___x_2033_, 1);
v___x_2034_ = lean_box(0);
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2018_, v___x_2035_);
v_i_2018_ = v___x_2036_;
v_b_2019_ = v___x_2034_;
goto _start;
}
else
{
lean_dec(v_declName_2015_);
return v___x_2033_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1___boxed(lean_object* v___x_2038_, lean_object* v_declName_2039_, lean_object* v_as_2040_, lean_object* v_sz_2041_, lean_object* v_i_2042_, lean_object* v_b_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
size_t v_sz_boxed_2047_; size_t v_i_boxed_2048_; lean_object* v_res_2049_; 
v_sz_boxed_2047_ = lean_unbox_usize(v_sz_2041_);
lean_dec(v_sz_2041_);
v_i_boxed_2048_ = lean_unbox_usize(v_i_2042_);
lean_dec(v_i_2042_);
v_res_2049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v___x_2038_, v_declName_2039_, v_as_2040_, v_sz_boxed_2047_, v_i_boxed_2048_, v_b_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec_ref(v_as_2040_);
lean_dec_ref(v___x_2038_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2050_, lean_object* v_x_2051_){
_start:
{
if (lean_obj_tag(v_x_2051_) == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_box(0);
return v___x_2052_;
}
else
{
lean_object* v_key_2053_; lean_object* v_value_2054_; lean_object* v_tail_2055_; uint8_t v___x_2056_; 
v_key_2053_ = lean_ctor_get(v_x_2051_, 0);
v_value_2054_ = lean_ctor_get(v_x_2051_, 1);
v_tail_2055_ = lean_ctor_get(v_x_2051_, 2);
v___x_2056_ = lean_name_eq(v_key_2053_, v_a_2050_);
if (v___x_2056_ == 0)
{
v_x_2051_ = v_tail_2055_;
goto _start;
}
else
{
lean_object* v___x_2058_; 
lean_inc(v_value_2054_);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_value_2054_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2059_, lean_object* v_x_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2059_, v_x_2060_);
lean_dec(v_x_2060_);
lean_dec(v_a_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(lean_object* v_m_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_buckets_2064_; lean_object* v___x_2065_; uint64_t v___y_2067_; 
v_buckets_2064_ = lean_ctor_get(v_m_2062_, 1);
v___x_2065_ = lean_array_get_size(v_buckets_2064_);
if (lean_obj_tag(v_a_2063_) == 0)
{
uint64_t v___x_2081_; 
v___x_2081_ = 1723ULL;
v___y_2067_ = v___x_2081_;
goto v___jp_2066_;
}
else
{
uint64_t v_hash_2082_; 
v_hash_2082_ = lean_ctor_get_uint64(v_a_2063_, sizeof(void*)*2);
v___y_2067_ = v_hash_2082_;
goto v___jp_2066_;
}
v___jp_2066_:
{
uint64_t v___x_2068_; uint64_t v___x_2069_; uint64_t v_fold_2070_; uint64_t v___x_2071_; uint64_t v___x_2072_; uint64_t v___x_2073_; size_t v___x_2074_; size_t v___x_2075_; size_t v___x_2076_; size_t v___x_2077_; size_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2068_ = 32ULL;
v___x_2069_ = lean_uint64_shift_right(v___y_2067_, v___x_2068_);
v_fold_2070_ = lean_uint64_xor(v___y_2067_, v___x_2069_);
v___x_2071_ = 16ULL;
v___x_2072_ = lean_uint64_shift_right(v_fold_2070_, v___x_2071_);
v___x_2073_ = lean_uint64_xor(v_fold_2070_, v___x_2072_);
v___x_2074_ = lean_uint64_to_usize(v___x_2073_);
v___x_2075_ = lean_usize_of_nat(v___x_2065_);
v___x_2076_ = ((size_t)1ULL);
v___x_2077_ = lean_usize_sub(v___x_2075_, v___x_2076_);
v___x_2078_ = lean_usize_land(v___x_2074_, v___x_2077_);
v___x_2079_ = lean_array_uget_borrowed(v_buckets_2064_, v___x_2078_);
v___x_2080_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2063_, v___x_2079_);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg___boxed(lean_object* v_m_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_m_2083_);
return v_res_2085_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__1));
v___x_2089_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__0));
v___x_2090_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2089_, v___x_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(lean_object* v_declName_2093_, uint8_t v_isMeta_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v_env_2102_; lean_object* v___y_2104_; lean_object* v___x_2117_; 
v___x_2098_ = lean_st_ref_get(v___y_2096_);
v_env_2102_ = lean_ctor_get(v___x_2098_, 0);
lean_inc_ref(v_env_2102_);
lean_dec(v___x_2098_);
v___x_2117_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2102_, v_declName_2093_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_dec_ref(v_env_2102_);
lean_dec(v_declName_2093_);
goto v___jp_2099_;
}
else
{
lean_object* v_val_2118_; lean_object* v___x_2119_; lean_object* v_modules_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_val_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_val_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2119_ = l_Lean_Environment_header(v_env_2102_);
v_modules_2120_ = lean_ctor_get(v___x_2119_, 3);
lean_inc_ref(v_modules_2120_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = lean_array_get_size(v_modules_2120_);
v___x_2122_ = lean_nat_dec_lt(v_val_2118_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_dec_ref(v_modules_2120_);
lean_dec(v_val_2118_);
lean_dec_ref(v_env_2102_);
lean_dec(v_declName_2093_);
goto v___jp_2099_;
}
else
{
lean_object* v___x_2123_; lean_object* v_env_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___y_2128_; 
v___x_2123_ = lean_st_ref_get(v___y_2096_);
v_env_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc_ref(v_env_2124_);
lean_dec(v___x_2123_);
v___x_2125_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__2);
v___x_2126_ = lean_array_fget(v_modules_2120_, v_val_2118_);
lean_dec(v_val_2118_);
lean_dec_ref(v_modules_2120_);
if (v_isMeta_2094_ == 0)
{
lean_dec_ref(v_env_2124_);
v___y_2128_ = v_isMeta_2094_;
goto v___jp_2127_;
}
else
{
uint8_t v___x_2139_; 
lean_inc(v_declName_2093_);
v___x_2139_ = l_Lean_isMarkedMeta(v_env_2124_, v_declName_2093_);
if (v___x_2139_ == 0)
{
v___y_2128_ = v_isMeta_2094_;
goto v___jp_2127_;
}
else
{
uint8_t v___x_2140_; 
v___x_2140_ = 0;
v___y_2128_ = v___x_2140_;
goto v___jp_2127_;
}
}
v___jp_2127_:
{
lean_object* v_toImport_2129_; lean_object* v_module_2130_; lean_object* v___x_2131_; 
v_toImport_2129_ = lean_ctor_get(v___x_2126_, 0);
lean_inc_ref(v_toImport_2129_);
lean_dec(v___x_2126_);
v_module_2130_ = lean_ctor_get(v_toImport_2129_, 0);
lean_inc(v_module_2130_);
lean_dec_ref(v_toImport_2129_);
lean_inc(v_declName_2093_);
v___x_2131_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0(v_module_2130_, v___y_2128_, v_declName_2093_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec_ref_known(v___x_2131_, 1);
v___x_2132_ = l_Lean_indirectModUseExt;
v___x_2133_ = lean_box(1);
v___x_2134_ = lean_box(0);
lean_inc_ref(v_env_2102_);
v___x_2135_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2125_, v___x_2132_, v_env_2102_, v___x_2133_, v___x_2134_);
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v___x_2135_, v_declName_2093_);
lean_dec(v___x_2135_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2137_; 
v___x_2137_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___closed__3));
v___y_2104_ = v___x_2137_;
goto v___jp_2103_;
}
else
{
lean_object* v_val_2138_; 
v_val_2138_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_val_2138_);
lean_dec_ref_known(v___x_2136_, 1);
v___y_2104_ = v_val_2138_;
goto v___jp_2103_;
}
}
else
{
lean_dec_ref(v_env_2102_);
lean_dec(v_declName_2093_);
return v___x_2131_;
}
}
}
}
v___jp_2099_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_box(0);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
v___jp_2103_:
{
lean_object* v___x_2105_; size_t v_sz_2106_; size_t v___x_2107_; lean_object* v___x_2108_; 
v___x_2105_ = lean_box(0);
v_sz_2106_ = lean_array_size(v___y_2104_);
v___x_2107_ = ((size_t)0ULL);
v___x_2108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__1(v_env_2102_, v_declName_2093_, v___y_2104_, v_sz_2106_, v___x_2107_, v___x_2105_, v___y_2095_, v___y_2096_);
lean_dec_ref(v___y_2104_);
lean_dec_ref(v_env_2102_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2108_, 0);
lean_dec(v_unused_2116_);
v___x_2110_ = v___x_2108_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_dec(v___x_2108_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2105_);
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2105_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
return v___x_2108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0___boxed(lean_object* v_declName_2141_, lean_object* v_isMeta_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
uint8_t v_isMeta_boxed_2146_; lean_object* v_res_2147_; 
v_isMeta_boxed_2146_ = lean_unbox(v_isMeta_2142_);
v_res_2147_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v_declName_2141_, v_isMeta_boxed_2146_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
return v_res_2147_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(lean_object* v_a_2148_, lean_object* v_x_2149_){
_start:
{
if (lean_obj_tag(v_x_2149_) == 0)
{
uint8_t v___x_2150_; 
v___x_2150_ = 0;
return v___x_2150_;
}
else
{
lean_object* v_head_2151_; lean_object* v_tail_2152_; uint8_t v___x_2153_; 
v_head_2151_ = lean_ctor_get(v_x_2149_, 0);
v_tail_2152_ = lean_ctor_get(v_x_2149_, 1);
v___x_2153_ = lean_name_eq(v_a_2148_, v_head_2151_);
if (v___x_2153_ == 0)
{
v_x_2149_ = v_tail_2152_;
goto _start;
}
else
{
return v___x_2153_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2___boxed(lean_object* v_a_2155_, lean_object* v_x_2156_){
_start:
{
uint8_t v_res_2157_; lean_object* v_r_2158_; 
v_res_2157_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v_a_2155_, v_x_2156_);
lean_dec(v_x_2156_);
lean_dec(v_a_2155_);
v_r_2158_ = lean_box(v_res_2157_);
return v_r_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(lean_object* v_t_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; lean_object* v_infoState_2163_; uint8_t v_enabled_2164_; 
v___x_2162_ = lean_st_ref_get(v___y_2160_);
v_infoState_2163_ = lean_ctor_get(v___x_2162_, 7);
lean_inc_ref(v_infoState_2163_);
lean_dec(v___x_2162_);
v_enabled_2164_ = lean_ctor_get_uint8(v_infoState_2163_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2163_);
if (v_enabled_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec_ref(v_t_2159_);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
else
{
lean_object* v___x_2167_; lean_object* v_infoState_2168_; lean_object* v_env_2169_; lean_object* v_nextMacroScope_2170_; lean_object* v_ngen_2171_; lean_object* v_auxDeclNGen_2172_; lean_object* v_traceState_2173_; lean_object* v_cache_2174_; lean_object* v_messages_2175_; lean_object* v_snapshotTasks_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2198_; 
v___x_2167_ = lean_st_ref_take(v___y_2160_);
v_infoState_2168_ = lean_ctor_get(v___x_2167_, 7);
v_env_2169_ = lean_ctor_get(v___x_2167_, 0);
v_nextMacroScope_2170_ = lean_ctor_get(v___x_2167_, 1);
v_ngen_2171_ = lean_ctor_get(v___x_2167_, 2);
v_auxDeclNGen_2172_ = lean_ctor_get(v___x_2167_, 3);
v_traceState_2173_ = lean_ctor_get(v___x_2167_, 4);
v_cache_2174_ = lean_ctor_get(v___x_2167_, 5);
v_messages_2175_ = lean_ctor_get(v___x_2167_, 6);
v_snapshotTasks_2176_ = lean_ctor_get(v___x_2167_, 8);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2178_ = v___x_2167_;
v_isShared_2179_ = v_isSharedCheck_2198_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snapshotTasks_2176_);
lean_inc(v_infoState_2168_);
lean_inc(v_messages_2175_);
lean_inc(v_cache_2174_);
lean_inc(v_traceState_2173_);
lean_inc(v_auxDeclNGen_2172_);
lean_inc(v_ngen_2171_);
lean_inc(v_nextMacroScope_2170_);
lean_inc(v_env_2169_);
lean_dec(v___x_2167_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2198_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
uint8_t v_enabled_2180_; lean_object* v_assignment_2181_; lean_object* v_lazyAssignment_2182_; lean_object* v_trees_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2197_; 
v_enabled_2180_ = lean_ctor_get_uint8(v_infoState_2168_, sizeof(void*)*3);
v_assignment_2181_ = lean_ctor_get(v_infoState_2168_, 0);
v_lazyAssignment_2182_ = lean_ctor_get(v_infoState_2168_, 1);
v_trees_2183_ = lean_ctor_get(v_infoState_2168_, 2);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_infoState_2168_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2185_ = v_infoState_2168_;
v_isShared_2186_ = v_isSharedCheck_2197_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_trees_2183_);
lean_inc(v_lazyAssignment_2182_);
lean_inc(v_assignment_2181_);
lean_dec(v_infoState_2168_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2197_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = l_Lean_PersistentArray_push___redArg(v_trees_2183_, v_t_2159_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 2, v___x_2187_);
v___x_2189_ = v___x_2185_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_assignment_2181_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_lazyAssignment_2182_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v___x_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2196_, sizeof(void*)*3, v_enabled_2180_);
v___x_2189_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 7, v___x_2189_);
v___x_2191_ = v___x_2178_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_env_2169_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_nextMacroScope_2170_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_ngen_2171_);
lean_ctor_set(v_reuseFailAlloc_2195_, 3, v_auxDeclNGen_2172_);
lean_ctor_set(v_reuseFailAlloc_2195_, 4, v_traceState_2173_);
lean_ctor_set(v_reuseFailAlloc_2195_, 5, v_cache_2174_);
lean_ctor_set(v_reuseFailAlloc_2195_, 6, v_messages_2175_);
lean_ctor_set(v_reuseFailAlloc_2195_, 7, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2195_, 8, v_snapshotTasks_2176_);
v___x_2191_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_st_ref_put(v___y_2160_, v___x_2191_);
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_t_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_2199_, v___y_2200_);
lean_dec(v___y_2200_);
return v_res_2202_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_unsigned_to_nat(32u);
v___x_2204_ = lean_mk_empty_array_with_capacity(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1(void){
_start:
{
size_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2206_ = ((size_t)5ULL);
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = lean_unsigned_to_nat(32u);
v___x_2209_ = lean_mk_empty_array_with_capacity(v___x_2208_);
v___x_2210_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__0);
v___x_2211_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
lean_ctor_set(v___x_2211_, 2, v___x_2207_);
lean_ctor_set(v___x_2211_, 3, v___x_2207_);
lean_ctor_set_usize(v___x_2211_, 4, v___x_2206_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(lean_object* v_t_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; lean_object* v_infoState_2217_; uint8_t v_enabled_2218_; 
v___x_2216_ = lean_st_ref_get(v___y_2214_);
v_infoState_2217_ = lean_ctor_get(v___x_2216_, 7);
lean_inc_ref(v_infoState_2217_);
lean_dec(v___x_2216_);
v_enabled_2218_ = lean_ctor_get_uint8(v_infoState_2217_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2217_);
if (v_enabled_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec_ref(v_t_2212_);
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___closed__1);
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_t_2212_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v___x_2222_, v___y_2214_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5___boxed(lean_object* v_t_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v_t_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
if (lean_obj_tag(v_a_2229_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = l_List_reverse___redArg(v_a_2230_);
return v___x_2231_;
}
else
{
lean_object* v_head_2232_; lean_object* v_tail_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2242_; 
v_head_2232_ = lean_ctor_get(v_a_2229_, 0);
v_tail_2233_ = lean_ctor_get(v_a_2229_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2229_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2235_ = v_a_2229_;
v_isShared_2236_ = v_isSharedCheck_2242_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_tail_2233_);
lean_inc(v_head_2232_);
lean_dec(v_a_2229_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2242_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = l_Lean_mkLevelParam(v_head_2232_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v_a_2230_);
lean_ctor_set(v___x_2235_, 0, v___x_2237_);
v___x_2239_ = v___x_2235_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_a_2230_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v_a_2229_ = v_tail_2233_;
v_a_2230_ = v___x_2239_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(lean_object* v_constName_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v_env_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; 
v___x_2247_ = lean_st_ref_get(v___y_2245_);
v_env_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc_ref(v_env_2248_);
lean_dec(v___x_2247_);
v___x_2249_ = 0;
lean_inc(v_constName_2243_);
v___x_2250_ = l_Lean_Environment_findConstVal_x3f(v_env_2248_, v_constName_2243_, v___x_2249_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3___redArg(v_constName_2243_, v___y_2244_, v___y_2245_);
return v___x_2251_;
}
else
{
lean_object* v_val_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_constName_2243_);
v_val_2252_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2250_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_val_2252_);
lean_dec(v___x_2250_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set_tag(v___x_2254_, 0);
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_val_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8___boxed(lean_object* v_constName_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(lean_object* v_constName_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
lean_inc(v_constName_2265_);
v___x_2269_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__8(v_constName_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2281_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_levelParams_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
v_levelParams_2274_ = lean_ctor_get(v_a_2270_, 1);
lean_inc(v_levelParams_2274_);
lean_dec(v_a_2270_);
v___x_2275_ = lean_box(0);
v___x_2276_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4_spec__9(v_levelParams_2274_, v___x_2275_);
v___x_2277_ = l_Lean_mkConst(v_constName_2265_, v___x_2276_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2277_);
v___x_2279_ = v___x_2272_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_constName_2265_);
v_a_2282_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2269_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2269_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4___boxed(lean_object* v_constName_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_constName_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(lean_object* v_stx_2295_, lean_object* v_n_2296_, lean_object* v_expectedType_x3f_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__4(v_n_2296_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v_stx_2295_);
v___x_2305_ = l_Lean_LocalContext_empty;
v___x_2306_ = 0;
v___x_2307_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2307_, 0, v___x_2304_);
lean_ctor_set(v___x_2307_, 1, v___x_2305_);
lean_ctor_set(v___x_2307_, 2, v_expectedType_x3f_2297_);
lean_ctor_set(v___x_2307_, 3, v_a_2302_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*4, v___x_2306_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*4 + 1, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
v___x_2309_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5(v___x_2308_, v___y_2298_, v___y_2299_);
return v___x_2309_;
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_expectedType_x3f_2297_);
lean_dec(v_stx_2295_);
v_a_2310_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2301_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2301_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1___boxed(lean_object* v_stx_2318_, lean_object* v_n_2319_, lean_object* v_expectedType_x3f_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_stx_2318_, v_n_2319_, v_expectedType_x3f_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2324_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__0));
v___x_2327_ = l_Lean_stringToMessageData(v___x_2326_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__2));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(lean_object* v_attrName_2331_, lean_object* v_extraKinds_2332_, uint8_t v_builtin_2333_, lean_object* v_stx_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_st_ref_get(v_a_2336_);
v___x_2339_ = l_Lean_Attribute_Builtin_getIdent(v_stx_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2418_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2418_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2418_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v_env_2344_; lean_object* v___x_2345_; lean_object* v___y_2347_; lean_object* v___y_2348_; 
v_env_2344_ = lean_ctor_get(v___x_2338_, 0);
lean_inc_ref(v_env_2344_);
lean_dec(v___x_2338_);
v___x_2345_ = l_Lean_Syntax_getId(v_a_2340_);
if (v_builtin_2333_ == 0)
{
goto v___jp_2395_;
}
else
{
uint8_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = 0;
lean_inc(v___x_2345_);
lean_inc_ref(v_env_2344_);
v___x_2417_ = l_Lean_Environment_find_x3f(v_env_2344_, v___x_2345_, v___x_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
goto v___jp_2395_;
}
else
{
lean_dec_ref_known(v___x_2417_, 1);
lean_dec_ref(v_env_2344_);
lean_dec(v_attrName_2331_);
v___y_2347_ = v_a_2335_;
v___y_2348_ = v_a_2336_;
goto v___jp_2346_;
}
}
v___jp_2346_:
{
lean_object* v___x_2349_; lean_object* v_env_2350_; uint8_t v___x_2351_; uint8_t v___x_2352_; 
v___x_2349_ = lean_st_ref_get(v___y_2348_);
v_env_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc_ref(v_env_2350_);
lean_dec(v___x_2349_);
v___x_2351_ = 1;
lean_inc(v___x_2345_);
v___x_2352_ = l_Lean_Environment_contains(v_env_2350_, v___x_2345_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2354_; 
lean_dec(v_a_2340_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2345_);
v___x_2354_ = v___x_2342_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2345_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
else
{
uint8_t v___x_2356_; lean_object* v___x_2357_; 
lean_del_object(v___x_2342_);
v___x_2356_ = 0;
lean_inc(v___x_2345_);
v___x_2357_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0(v___x_2345_, v___x_2356_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2385_; 
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v___x_2357_, 0);
lean_dec(v_unused_2386_);
v___x_2359_ = v___x_2357_;
v_isShared_2360_ = v_isSharedCheck_2385_;
goto v_resetjp_2358_;
}
else
{
lean_dec(v___x_2357_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2385_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v_infoState_2362_; uint8_t v_enabled_2363_; 
v___x_2361_ = lean_st_ref_get(v___y_2348_);
v_infoState_2362_ = lean_ctor_get(v___x_2361_, 7);
lean_inc_ref(v_infoState_2362_);
lean_dec(v___x_2361_);
v_enabled_2363_ = lean_ctor_get_uint8(v_infoState_2362_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2362_);
if (v_enabled_2363_ == 0)
{
lean_object* v___x_2365_; 
lean_dec(v_a_2340_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2345_);
v___x_2365_ = v___x_2359_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2345_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_del_object(v___x_2359_);
v___x_2367_ = lean_box(0);
lean_inc(v___x_2345_);
v___x_2368_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1(v_a_2340_, v___x_2345_, v___x_2367_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v___x_2368_, 0);
lean_dec(v_unused_2376_);
v___x_2370_ = v___x_2368_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_dec(v___x_2368_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2345_);
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2345_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v___x_2345_);
v_a_2377_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2368_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2368_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v___x_2345_);
lean_dec(v_a_2340_);
v_a_2387_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2357_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2357_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
v___jp_2395_:
{
uint8_t v___x_2396_; 
lean_inc(v___x_2345_);
v___x_2396_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2344_, v___x_2345_);
if (v___x_2396_ == 0)
{
uint8_t v___x_2397_; 
v___x_2397_ = l_List_elem___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__2(v___x_2345_, v_extraKinds_2332_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_del_object(v___x_2342_);
lean_dec(v_a_2340_);
v___x_2398_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__1);
v___x_2399_ = l_Lean_MessageData_ofName(v_attrName_2331_);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___closed__3);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = l_Lean_MessageData_ofName(v___x_2345_);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__3);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v___x_2406_, v_a_2335_, v_a_2336_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
lean_dec(v_attrName_2331_);
v___y_2347_ = v_a_2335_;
v___y_2348_ = v_a_2336_;
goto v___jp_2346_;
}
}
else
{
lean_dec(v_attrName_2331_);
v___y_2347_ = v_a_2335_;
v___y_2348_ = v_a_2336_;
goto v___jp_2346_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v___x_2338_);
lean_dec(v_attrName_2331_);
v_a_2419_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2339_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2339_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed(lean_object* v_attrName_2427_, lean_object* v_extraKinds_2428_, lean_object* v_builtin_2429_, lean_object* v_stx_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
uint8_t v_builtin_boxed_2434_; lean_object* v_res_2435_; 
v_builtin_boxed_2434_ = lean_unbox(v_builtin_2429_);
v_res_2435_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey(v_attrName_2427_, v_extraKinds_2428_, v_builtin_boxed_2434_, v_stx_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_extraKinds_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(lean_object* v_00_u03b2_2436_, lean_object* v_m_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_2437_, v_a_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2440_, lean_object* v_m_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2(v_00_u03b2_2440_, v_m_2441_, v_a_2442_);
lean_dec(v_a_2442_);
lean_dec_ref(v_m_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(lean_object* v_t_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___redArg(v_t_2444_, v___y_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11___boxed(lean_object* v_t_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__1_spec__5_spec__11(v_t_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2453_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2454_, lean_object* v_x_2455_, lean_object* v_x_2456_){
_start:
{
uint8_t v___x_2457_; 
v___x_2457_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___redArg(v_x_2455_, v_x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2458_, lean_object* v_x_2459_, lean_object* v_x_2460_){
_start:
{
uint8_t v_res_2461_; lean_object* v_r_2462_; 
v_res_2461_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1(v_00_u03b2_2458_, v_x_2459_, v_x_2460_);
lean_dec_ref(v_x_2460_);
lean_dec_ref(v_x_2459_);
v_r_2462_ = lean_box(v_res_2461_);
return v_r_2462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2463_, lean_object* v_a_2464_, lean_object* v_x_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___redArg(v_a_2464_, v_x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2467_, lean_object* v_a_2468_, lean_object* v_x_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2_spec__5(v_00_u03b2_2467_, v_a_2468_, v_x_2469_);
lean_dec(v_x_2469_);
lean_dec(v_a_2468_);
return v_res_2470_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_2471_, lean_object* v_x_2472_, size_t v_x_2473_, lean_object* v_x_2474_){
_start:
{
uint8_t v___x_2475_; 
v___x_2475_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___redArg(v_x_2472_, v_x_2473_, v_x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_, lean_object* v_x_2479_){
_start:
{
size_t v_x_6126__boxed_2480_; uint8_t v_res_2481_; lean_object* v_r_2482_; 
v_x_6126__boxed_2480_ = lean_unbox_usize(v_x_2478_);
lean_dec(v_x_2478_);
v_res_2481_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_2476_, v_x_2477_, v_x_6126__boxed_2480_, v_x_2479_);
lean_dec_ref(v_x_2479_);
lean_dec_ref(v_x_2477_);
v_r_2482_ = lean_box(v_res_2481_);
return v_r_2482_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_2483_, lean_object* v_keys_2484_, lean_object* v_vals_2485_, lean_object* v_heq_2486_, lean_object* v_i_2487_, lean_object* v_k_2488_){
_start:
{
uint8_t v___x_2489_; 
v___x_2489_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_2484_, v_i_2487_, v_k_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_2490_, lean_object* v_keys_2491_, lean_object* v_vals_2492_, lean_object* v_heq_2493_, lean_object* v_i_2494_, lean_object* v_k_2495_){
_start:
{
uint8_t v_res_2496_; lean_object* v_r_2497_; 
v_res_2496_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__1_spec__4_spec__10(v_00_u03b2_2490_, v_keys_2491_, v_vals_2492_, v_heq_2493_, v_i_2494_, v_k_2495_);
lean_dec_ref(v_k_2495_);
lean_dec_ref(v_vals_2492_);
lean_dec_ref(v_keys_2491_);
v_r_2497_ = lean_box(v_res_2496_);
return v_r_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(uint8_t v_builtin_2498_, lean_object* v_declName_2499_, lean_object* v_key_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2____boxed(lean_object* v_builtin_2506_, lean_object* v_declName_2507_, lean_object* v_key_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
uint8_t v_builtin_boxed_2512_; lean_object* v_res_2513_; 
v_builtin_boxed_2512_ = lean_unbox(v_builtin_2506_);
v_res_2513_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(v_builtin_boxed_2512_, v_declName_2507_, v_key_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v_key_2508_);
lean_dec(v_declName_2507_);
return v_res_2513_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_box(0);
v___x_2526_ = l_Lean_Fmt_headerKind;
v___x_2527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_);
v___x_2529_ = l_Lean_Fmt_cmdsKind;
v___x_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_);
v___x_2532_ = l_Lean_Fmt_moduleKind;
v___x_2533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___x_2531_);
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_);
v___x_2535_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_));
v___x_2536_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey___boxed), 7, 2);
lean_closure_set(v___x_2536_, 0, v___x_2535_);
lean_closure_set(v___x_2536_, 1, v___x_2534_);
return v___x_2536_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___f_2537_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_));
v___x_2538_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_);
v___x_2539_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_));
v___x_2540_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_));
v___x_2541_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_));
v___x_2542_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_));
v___x_2543_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2541_);
lean_ctor_set(v___x_2543_, 2, v___x_2540_);
lean_ctor_set(v___x_2543_, 3, v___x_2539_);
lean_ctor_set(v___x_2543_, 4, v___x_2538_);
lean_ctor_set(v___x_2543_, 5, v___f_2537_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_);
v___x_2551_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__13_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_));
v___x_2552_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_2550_, v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2____boxed(lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_();
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(lean_object* v_constName_2560_, lean_object* v_env_2561_, lean_object* v_opts_2562_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
v___x_2564_ = l_Lean_Environment_evalConstCheck___redArg(v_env_2561_, v_opts_2562_, v___x_2563_, v_constName_2560_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___boxed(lean_object* v_constName_2565_, lean_object* v_env_2566_, lean_object* v_opts_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1(v_constName_2565_, v_env_2566_, v_opts_2567_);
lean_dec_ref(v_opts_2567_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(lean_object* v_constName_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_env_2572_; lean_object* v_opts_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_env_2572_ = lean_ctor_get(v_a_2570_, 0);
v_opts_2573_ = lean_ctor_get(v_a_2570_, 1);
v___x_2574_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__1));
lean_inc_ref(v_env_2572_);
v___x_2575_ = l_Lean_Environment_evalConstCheck___redArg(v_env_2572_, v_opts_2573_, v___x_2574_, v_constName_2569_);
v___x_2576_ = l_IO_ofExcept___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_spec__0___redArg(v___x_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn___boxed(lean_object* v_constName_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_constName_2577_, v_a_2578_);
lean_dec_ref(v_a_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_));
v___x_2585_ = lean_st_mk_ref(v___x_2584_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2____boxed(lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn(lean_object* v_f_2589_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2591_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___x_2592_ = lean_st_ref_take(v___x_2591_);
v___x_2593_ = lean_array_push(v___x_2592_, v_f_2589_);
v___x_2594_ = lean_st_ref_put(v___x_2591_, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_addBuiltinStickyTermFn___boxed(lean_object* v_f_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_Fmt_addBuiltinStickyTermFn(v_f_2596_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object* v_x_2599_){
_start:
{
lean_object* v_fst_2600_; 
v_fst_2600_ = lean_ctor_get(v_x_2599_, 0);
lean_inc(v_fst_2600_);
return v_fst_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object* v_x_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(v_x_2601_);
lean_dec_ref(v_x_2601_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object* v_x_2603_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_box(0);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object* v_x_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(v_x_2605_);
lean_dec_ref(v_x_2605_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object* v_x_2607_, lean_object* v_s_2608_){
_start:
{
lean_object* v_fst_2609_; lean_object* v___x_2610_; 
v_fst_2609_ = lean_ctor_get(v_s_2608_, 0);
lean_inc_n(v_fst_2609_, 3);
v___x_2610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2610_, 0, v_fst_2609_);
lean_ctor_set(v___x_2610_, 1, v_fst_2609_);
lean_ctor_set(v___x_2610_, 2, v_fst_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object* v_x_2611_, lean_object* v_s_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(v_x_2611_, v_s_2612_);
lean_dec_ref(v_s_2612_);
lean_dec_ref(v_x_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__3_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object* v_x_2614_, lean_object* v_x_2615_){
_start:
{
lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v_fst_2618_; lean_object* v_snd_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2628_; 
v_fst_2616_ = lean_ctor_get(v_x_2614_, 0);
lean_inc(v_fst_2616_);
v_snd_2617_ = lean_ctor_get(v_x_2614_, 1);
lean_inc(v_snd_2617_);
lean_dec_ref(v_x_2614_);
v_fst_2618_ = lean_ctor_get(v_x_2615_, 0);
v_snd_2619_ = lean_ctor_get(v_x_2615_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_x_2615_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2621_ = v_x_2615_;
v_isShared_2622_ = v_isSharedCheck_2628_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_snd_2619_);
lean_inc(v_fst_2618_);
lean_dec(v_x_2615_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2628_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2623_ = lean_array_push(v_fst_2616_, v_fst_2618_);
v___x_2624_ = lean_array_push(v_snd_2617_, v_snd_2619_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 1, v___x_2624_);
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2626_ = v___x_2621_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object* v___x_2629_, lean_object* v___x_2630_){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2632_ = lean_st_ref_get(v___x_2629_);
v___x_2633_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
lean_ctor_set(v___x_2634_, 1, v___x_2632_);
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object* v___x_2636_, lean_object* v___x_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(v___x_2636_, v___x_2637_);
lean_dec(v___x_2637_);
lean_dec(v___x_2636_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__0(lean_object* v_as_2640_, size_t v_i_2641_, size_t v_stop_2642_, lean_object* v_b_2643_, lean_object* v___y_2644_){
_start:
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_usize_dec_eq(v_i_2641_, v_stop_2642_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_array_uget_borrowed(v_as_2640_, v_i_2641_);
lean_inc(v___x_2647_);
v___x_2648_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v___x_2647_, v___y_2644_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2650_; size_t v___x_2651_; size_t v___x_2652_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v___x_2650_ = lean_array_push(v_b_2643_, v_a_2649_);
v___x_2651_ = ((size_t)1ULL);
v___x_2652_ = lean_usize_add(v_i_2641_, v___x_2651_);
v_i_2641_ = v___x_2652_;
v_b_2643_ = v___x_2650_;
goto _start;
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_b_2643_);
v_a_2654_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2648_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2648_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_b_2643_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_2663_, lean_object* v_i_2664_, lean_object* v_stop_2665_, lean_object* v_b_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
size_t v_i_boxed_2669_; size_t v_stop_boxed_2670_; lean_object* v_res_2671_; 
v_i_boxed_2669_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_stop_boxed_2670_ = lean_unbox_usize(v_stop_2665_);
lean_dec(v_stop_2665_);
v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__0(v_as_2663_, v_i_boxed_2669_, v_stop_boxed_2670_, v_b_2666_, v___y_2667_);
lean_dec_ref(v___y_2667_);
lean_dec_ref(v_as_2663_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__1(lean_object* v_as_2672_, size_t v_i_2673_, size_t v_stop_2674_, lean_object* v_b_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_a_2679_; lean_object* v___y_2684_; uint8_t v___x_2686_; 
v___x_2686_ = lean_usize_dec_eq(v_i_2673_, v_stop_2674_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2687_ = lean_unsigned_to_nat(0u);
v___x_2688_ = lean_array_uget_borrowed(v_as_2672_, v_i_2673_);
v___x_2689_ = lean_array_get_size(v___x_2688_);
v___x_2690_ = lean_nat_dec_lt(v___x_2687_, v___x_2689_);
if (v___x_2690_ == 0)
{
v_a_2679_ = v_b_2675_;
goto v___jp_2678_;
}
else
{
uint8_t v___x_2691_; 
v___x_2691_ = lean_nat_dec_le(v___x_2689_, v___x_2689_);
if (v___x_2691_ == 0)
{
if (v___x_2690_ == 0)
{
v_a_2679_ = v_b_2675_;
goto v___jp_2678_;
}
else
{
size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = ((size_t)0ULL);
v___x_2693_ = lean_usize_of_nat(v___x_2689_);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__0(v___x_2688_, v___x_2692_, v___x_2693_, v_b_2675_, v___y_2676_);
v___y_2684_ = v___x_2694_;
goto v___jp_2683_;
}
}
else
{
size_t v___x_2695_; size_t v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = lean_usize_of_nat(v___x_2689_);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__0(v___x_2688_, v___x_2695_, v___x_2696_, v_b_2675_, v___y_2676_);
v___y_2684_ = v___x_2697_;
goto v___jp_2683_;
}
}
}
else
{
lean_object* v___x_2698_; 
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_b_2675_);
return v___x_2698_;
}
v___jp_2678_:
{
size_t v___x_2680_; size_t v___x_2681_; 
v___x_2680_ = ((size_t)1ULL);
v___x_2681_ = lean_usize_add(v_i_2673_, v___x_2680_);
v_i_2673_ = v___x_2681_;
v_b_2675_ = v_a_2679_;
goto _start;
}
v___jp_2683_:
{
if (lean_obj_tag(v___y_2684_) == 0)
{
lean_object* v_a_2685_; 
v_a_2685_ = lean_ctor_get(v___y_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___y_2684_, 1);
v_a_2679_ = v_a_2685_;
goto v___jp_2678_;
}
else
{
return v___y_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_2699_, lean_object* v_i_2700_, lean_object* v_stop_2701_, lean_object* v_b_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
size_t v_i_boxed_2705_; size_t v_stop_boxed_2706_; lean_object* v_res_2707_; 
v_i_boxed_2705_ = lean_unbox_usize(v_i_2700_);
lean_dec(v_i_2700_);
v_stop_boxed_2706_ = lean_unbox_usize(v_stop_2701_);
lean_dec(v_stop_2701_);
v_res_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__1(v_as_2699_, v_i_boxed_2705_, v_stop_boxed_2706_, v_b_2702_, v___y_2703_);
lean_dec_ref(v___y_2703_);
lean_dec_ref(v_as_2699_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(lean_object* v___x_2708_, lean_object* v___x_2709_, lean_object* v_as_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_a_2714_; lean_object* v___y_2719_; lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = lean_st_ref_get(v___x_2708_);
v___x_2730_ = lean_array_get_size(v_as_2710_);
v___x_2731_ = lean_nat_dec_lt(v___x_2709_, v___x_2730_);
if (v___x_2731_ == 0)
{
v_a_2714_ = v___x_2729_;
goto v___jp_2713_;
}
else
{
uint8_t v___x_2732_; 
v___x_2732_ = lean_nat_dec_le(v___x_2730_, v___x_2730_);
if (v___x_2732_ == 0)
{
if (v___x_2731_ == 0)
{
v_a_2714_ = v___x_2729_;
goto v___jp_2713_;
}
else
{
size_t v___x_2733_; size_t v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = lean_usize_of_nat(v___x_2730_);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__1(v_as_2710_, v___x_2733_, v___x_2734_, v___x_2729_, v___y_2711_);
v___y_2719_ = v___x_2735_;
goto v___jp_2718_;
}
}
else
{
size_t v___x_2736_; size_t v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = ((size_t)0ULL);
v___x_2737_ = lean_usize_of_nat(v___x_2730_);
v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__spec__1(v_as_2710_, v___x_2736_, v___x_2737_, v___x_2729_, v___y_2711_);
v___y_2719_ = v___x_2738_;
goto v___jp_2718_;
}
}
v___jp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_mk_empty_array_with_capacity(v___x_2709_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v_a_2714_);
v___x_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
return v___x_2717_;
}
v___jp_2718_:
{
if (lean_obj_tag(v___y_2719_) == 0)
{
lean_object* v_a_2720_; 
v_a_2720_ = lean_ctor_get(v___y_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___y_2719_, 1);
v_a_2714_ = v_a_2720_;
goto v___jp_2713_;
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
v_a_2721_ = lean_ctor_get(v___y_2719_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___y_2719_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___y_2719_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___y_2719_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object* v___x_2739_, lean_object* v___x_2740_, lean_object* v_as_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(v___x_2739_, v___x_2740_, v_as_2741_, v___y_2742_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v_as_2741_);
lean_dec(v___x_2740_);
lean_dec(v___x_2739_);
return v_res_2744_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___f_2755_; 
v___x_2753_ = lean_unsigned_to_nat(0u);
v___x_2754_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___f_2755_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__4_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed), 3, 2);
lean_closure_set(v___f_2755_, 0, v___x_2754_);
lean_closure_set(v___f_2755_, 1, v___x_2753_);
return v___f_2755_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___f_2758_; 
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef;
v___f_2758_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_2758_, 0, v___x_2757_);
lean_closure_set(v___f_2758_, 1, v___x_2756_);
return v___f_2758_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___f_2761_; lean_object* v___f_2762_; lean_object* v___f_2763_; lean_object* v___f_2764_; lean_object* v___f_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2759_ = lean_box(0);
v___x_2760_ = lean_box(2);
v___f_2761_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_));
v___f_2762_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_));
v___f_2763_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_));
v___f_2764_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_);
v___f_2765_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_);
v___x_2766_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_));
v___x_2767_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___f_2765_);
lean_ctor_set(v___x_2767_, 2, v___f_2764_);
lean_ctor_set(v___x_2767_, 3, v___f_2763_);
lean_ctor_set(v___x_2767_, 4, v___f_2762_);
lean_ctor_set(v___x_2767_, 5, v___f_2761_);
lean_ctor_set(v___x_2767_, 6, v___x_2760_);
lean_ctor_set(v___x_2767_, 7, v___x_2759_);
return v___x_2767_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___f_2768_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_));
v___x_2769_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v___f_2768_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_);
v___x_2773_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2____boxed(lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_();
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(lean_object* v_name_2776_, lean_object* v_decl_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2781_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_2782_ = l_Lean_MessageData_ofName(v_name_2776_);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_);
v___x_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = l_Lean_throwError___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__0___redArg(v___x_2785_, v___y_2778_, v___y_2779_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed(lean_object* v_name_2787_, lean_object* v_decl_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(v_name_2787_, v_decl_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v_decl_2788_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(uint8_t v_builtin_2794_, lean_object* v___x_2795_, lean_object* v___x_2796_, lean_object* v___x_2797_, lean_object* v_name_2798_, lean_object* v_decl_2799_, lean_object* v_stx_2800_, uint8_t v_kind_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2800_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec_ref_known(v___x_2869_, 1);
if (v_builtin_2794_ == 0)
{
lean_object* v___x_2870_; 
lean_inc(v_decl_2799_);
lean_inc(v_name_2798_);
v___x_2870_ = l_Lean_ensureAttrDeclIsMeta(v_name_2798_, v_decl_2799_, v_kind_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_dec_ref_known(v___x_2870_, 1);
v___y_2864_ = v___y_2802_;
v___y_2865_ = v___y_2803_;
goto v___jp_2863_;
}
else
{
lean_dec(v_decl_2799_);
lean_dec(v_name_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___x_2796_);
lean_dec(v___x_2795_);
return v___x_2870_;
}
}
else
{
v___y_2864_ = v___y_2802_;
v___y_2865_ = v___y_2803_;
goto v___jp_2863_;
}
}
else
{
lean_dec(v_decl_2799_);
lean_dec(v_name_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___x_2796_);
lean_dec(v___x_2795_);
return v___x_2869_;
}
v___jp_2805_:
{
if (v_builtin_2794_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v_toCold_2810_; lean_object* v_env_2811_; lean_object* v_ref_2812_; lean_object* v_options_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___x_2796_);
v___x_2808_ = lean_st_ref_get(v___y_2807_);
v___x_2809_ = lean_st_ref_get(v___y_2807_);
v_toCold_2810_ = lean_ctor_get(v___y_2806_, 0);
v_env_2811_ = lean_ctor_get(v___x_2809_, 0);
lean_inc_ref(v_env_2811_);
lean_dec(v___x_2809_);
v_ref_2812_ = lean_ctor_get(v___y_2806_, 2);
v_options_2813_ = lean_ctor_get(v_toCold_2810_, 2);
lean_inc_ref(v_options_2813_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v_env_2811_);
lean_ctor_set(v___x_2814_, 1, v_options_2813_);
lean_inc(v_decl_2799_);
v___x_2815_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn(v_decl_2799_, v___x_2814_);
lean_dec_ref_known(v___x_2814_, 2);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v_env_2817_; lean_object* v___x_2818_; lean_object* v_toEnvExtension_2819_; lean_object* v_asyncMode_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v_env_2817_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2817_);
lean_dec(v___x_2808_);
v___x_2818_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_2819_ = lean_ctor_get(v___x_2818_, 0);
v_asyncMode_2820_ = lean_ctor_get(v_toEnvExtension_2819_, 2);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_decl_2799_);
lean_ctor_set(v___x_2821_, 1, v_a_2816_);
v___x_2822_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2818_, v_env_2817_, v___x_2821_, v_asyncMode_2820_, v___x_2795_);
v___x_2823_ = l_Lean_setEnv___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__1___redArg(v___x_2822_, v___y_2807_);
return v___x_2823_;
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v___x_2808_);
lean_dec(v_decl_2799_);
lean_dec(v___x_2795_);
v_a_2824_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2826_ = v___x_2815_;
v_isShared_2827_ = v_isSharedCheck_2835_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2815_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2835_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2828_ = lean_io_error_to_string(v_a_2824_);
v___x_2829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
v___x_2830_ = l_Lean_MessageData_ofFormat(v___x_2829_);
lean_inc(v_ref_2812_);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_ref_2812_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2831_);
v___x_2833_ = v___x_2826_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_dec(v___x_2795_);
v___x_2836_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_));
v___x_2837_ = l_Lean_Name_mkStr3(v___x_2796_, v___x_2797_, v___x_2836_);
v___x_2838_ = lean_box(0);
v___x_2839_ = l_Lean_mkConst(v___x_2837_, v___x_2838_);
lean_inc(v_decl_2799_);
v___x_2840_ = l_Lean_mkConst(v_decl_2799_, v___x_2838_);
v___x_2841_ = l_Lean_Expr_app___override(v___x_2839_, v___x_2840_);
v___x_2842_ = l_Lean_declareBuiltin(v_decl_2799_, v___x_2841_, v___y_2806_, v___y_2807_);
return v___x_2842_;
}
}
v___jp_2843_:
{
lean_object* v___x_2846_; 
lean_inc(v_decl_2799_);
v___x_2846_ = l_Lean_getConstInfo___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__2(v_decl_2799_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l_Lean_ConstantInfo_type(v_a_2847_);
lean_dec(v_a_2847_);
v___x_2849_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkStickyTermFn_unsafe__1___closed__0));
lean_inc_ref(v___x_2797_);
lean_inc_ref(v___x_2796_);
v___x_2850_ = l_Lean_Name_mkStr3(v___x_2796_, v___x_2797_, v___x_2849_);
v___x_2851_ = l_Lean_Expr_isConstOf(v___x_2848_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___x_2796_);
lean_dec(v___x_2795_);
v___x_2852_ = lean_box(0);
v___x_2853_ = l_Lean_mkConst(v___x_2850_, v___x_2852_);
v___x_2854_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__3___redArg(v_name_2798_, v_decl_2799_, v___x_2848_, v___x_2853_, v___y_2844_, v___y_2845_);
return v___x_2854_;
}
else
{
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2848_);
lean_dec(v_name_2798_);
v___y_2806_ = v___y_2844_;
v___y_2807_ = v___y_2845_;
goto v___jp_2805_;
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_decl_2799_);
lean_dec(v_name_2798_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___x_2796_);
lean_dec(v___x_2795_);
v_a_2855_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2846_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2846_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
v___jp_2863_:
{
uint8_t v___x_2866_; uint8_t v___x_2867_; 
v___x_2866_ = 0;
v___x_2867_ = l_Lean_instBEqAttributeKind_beq(v_kind_2801_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; 
lean_dec(v_decl_2799_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___x_2796_);
lean_dec(v___x_2795_);
v___x_2868_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2__spec__4___redArg(v_name_2798_, v_kind_2801_, v___y_2864_, v___y_2865_);
return v___x_2868_;
}
else
{
v___y_2844_ = v___y_2864_;
v___y_2845_ = v___y_2865_;
goto v___jp_2843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed(lean_object* v_builtin_2871_, lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, lean_object* v_name_2875_, lean_object* v_decl_2876_, lean_object* v_stx_2877_, lean_object* v_kind_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
uint8_t v_builtin_boxed_2882_; uint8_t v_kind_boxed_2883_; lean_object* v_res_2884_; 
v_builtin_boxed_2882_ = lean_unbox(v_builtin_2871_);
v_kind_boxed_2883_ = lean_unbox(v_kind_2878_);
v_res_2884_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(v_builtin_boxed_2882_, v___x_2872_, v___x_2873_, v___x_2874_, v_name_2875_, v_decl_2876_, v_stx_2877_, v_kind_boxed_2883_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2884_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = lean_unsigned_to_nat(2308933963u);
v___x_2886_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_2887_ = l_Lean_Name_num___override(v___x_2886_, v___x_2885_);
return v___x_2887_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__9_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_2889_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_);
v___x_2890_ = l_Lean_Name_str___override(v___x_2889_, v___x_2888_);
return v___x_2890_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__11_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_));
v___x_2892_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_);
v___x_2893_ = l_Lean_Name_str___override(v___x_2892_, v___x_2891_);
return v___x_2893_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = lean_unsigned_to_nat(2u);
v___x_2895_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_);
v___x_2896_ = l_Lean_Name_num___override(v___x_2895_, v___x_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(uint8_t v_builtin_2899_, lean_object* v_name_2900_){
_start:
{
lean_object* v___f_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___f_2907_; lean_object* v___x_2908_; lean_object* v___y_2910_; 
lean_inc_n(v_name_2900_, 2);
v___f_2902_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_2902_, 0, v_name_2900_);
v___x_2903_ = lean_box(0);
v___x_2904_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__0));
v___x_2905_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_mkFmtProvider_unsafe__1___closed__1));
v___x_2906_ = lean_box(v_builtin_2899_);
v___f_2907_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(v___f_2907_, 0, v___x_2906_);
lean_closure_set(v___f_2907_, 1, v___x_2903_);
lean_closure_set(v___f_2907_, 2, v___x_2904_);
lean_closure_set(v___f_2907_, 3, v___x_2905_);
lean_closure_set(v___f_2907_, 4, v_name_2900_);
v___x_2908_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_);
if (v_builtin_2899_ == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__0_spec__2___closed__1));
v___y_2910_ = v___x_2917_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2918_; 
v___x_2918_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__5_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_));
v___y_2910_ = v___x_2918_;
goto v___jp_2909_;
}
v___jp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2911_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2___closed__4_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_));
lean_inc_ref(v___y_2910_);
v___x_2912_ = lean_string_append(v___y_2910_, v___x_2911_);
v___x_2913_ = 1;
v___x_2914_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2914_, 0, v___x_2908_);
lean_ctor_set(v___x_2914_, 1, v_name_2900_);
lean_ctor_set(v___x_2914_, 2, v___x_2912_);
lean_ctor_set_uint8(v___x_2914_, sizeof(void*)*3, v___x_2913_);
v___x_2915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v___f_2907_);
lean_ctor_set(v___x_2915_, 2, v___f_2902_);
v___x_2916_ = l_Lean_registerBuiltinAttribute(v___x_2915_);
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed(lean_object* v_builtin_2919_, lean_object* v_name_2920_, lean_object* v___y_2921_){
_start:
{
uint8_t v_builtin_boxed_2922_; lean_object* v_res_2923_; 
v_builtin_boxed_2922_ = lean_unbox(v_builtin_2919_);
v_res_2923_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(v_builtin_boxed_2922_, v_name_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = 1;
v___x_2932_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_));
v___x_2933_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(v___x_2931_, v___x_2932_);
if (lean_obj_tag(v___x_2933_) == 0)
{
uint8_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec_ref_known(v___x_2933_, 1);
v___x_2934_ = 0;
v___x_2935_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_));
v___x_2936_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___lam__2_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_(v___x_2934_, v___x_2935_);
return v___x_2936_;
}
else
{
return v___x_2933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2____boxed(lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_();
return v_res_2938_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(lean_object* v_t_2939_, lean_object* v_as_2940_, size_t v_i_2941_, size_t v_stop_2942_){
_start:
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_usize_dec_eq(v_i_2941_, v_stop_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_157__overap_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_157__overap_2944_ = lean_array_uget_borrowed(v_as_2940_, v_i_2941_);
lean_inc(v___x_157__overap_2944_);
lean_inc(v_t_2939_);
v___x_2945_ = lean_apply_1(v___x_157__overap_2944_, v_t_2939_);
v___x_2946_ = lean_unbox(v___x_2945_);
if (v___x_2946_ == 0)
{
size_t v___x_2947_; size_t v___x_2948_; 
v___x_2947_ = ((size_t)1ULL);
v___x_2948_ = lean_usize_add(v_i_2941_, v___x_2947_);
v_i_2941_ = v___x_2948_;
goto _start;
}
else
{
uint8_t v___x_2950_; 
lean_dec(v_t_2939_);
v___x_2950_ = lean_unbox(v___x_2945_);
return v___x_2950_;
}
}
else
{
uint8_t v___x_2951_; 
lean_dec(v_t_2939_);
v___x_2951_ = 0;
return v___x_2951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0___boxed(lean_object* v_t_2952_, lean_object* v_as_2953_, lean_object* v_i_2954_, lean_object* v_stop_2955_){
_start:
{
size_t v_i_boxed_2956_; size_t v_stop_boxed_2957_; uint8_t v_res_2958_; lean_object* v_r_2959_; 
v_i_boxed_2956_ = lean_unbox_usize(v_i_2954_);
lean_dec(v_i_2954_);
v_stop_boxed_2957_ = lean_unbox_usize(v_stop_2955_);
lean_dec(v_stop_2955_);
v_res_2958_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_2952_, v_as_2953_, v_i_boxed_2956_, v_stop_boxed_2957_);
lean_dec_ref(v_as_2953_);
v_r_2959_ = lean_box(v_res_2958_);
return v_r_2959_;
}
}
static lean_object* _init_l_Lean_Fmt_propagatesRhsStickiness___closed__0(void){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Array_instInhabited(lean_box(0));
return v___x_2960_;
}
}
static lean_object* _init_l_Lean_Fmt_propagatesRhsStickiness___closed__1(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_obj_once(&l_Lean_Fmt_propagatesRhsStickiness___closed__0, &l_Lean_Fmt_propagatesRhsStickiness___closed__0_once, _init_l_Lean_Fmt_propagatesRhsStickiness___closed__0);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_propagatesRhsStickiness(lean_object* v_env_2963_, lean_object* v_t_2964_){
_start:
{
lean_object* v___x_2965_; lean_object* v_toEnvExtension_2966_; lean_object* v_asyncMode_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_snd_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2965_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt;
v_toEnvExtension_2966_ = lean_ctor_get(v___x_2965_, 0);
v_asyncMode_2967_ = lean_ctor_get(v_toEnvExtension_2966_, 2);
v___x_2968_ = lean_obj_once(&l_Lean_Fmt_propagatesRhsStickiness___closed__1, &l_Lean_Fmt_propagatesRhsStickiness___closed__1_once, _init_l_Lean_Fmt_propagatesRhsStickiness___closed__1);
v___x_2969_ = lean_box(0);
v___x_2970_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2968_, v___x_2965_, v_env_2963_, v_asyncMode_2967_, v___x_2969_);
v_snd_2971_ = lean_ctor_get(v___x_2970_, 1);
lean_inc(v_snd_2971_);
lean_dec(v___x_2970_);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = lean_array_get_size(v_snd_2971_);
v___x_2974_ = lean_nat_dec_lt(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_dec(v_snd_2971_);
lean_dec(v_t_2964_);
return v___x_2974_;
}
else
{
if (v___x_2974_ == 0)
{
lean_dec(v_snd_2971_);
lean_dec(v_t_2964_);
return v___x_2974_;
}
else
{
size_t v___x_2975_; size_t v___x_2976_; uint8_t v___x_2977_; 
v___x_2975_ = ((size_t)0ULL);
v___x_2976_ = lean_usize_of_nat(v___x_2973_);
v___x_2977_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_propagatesRhsStickiness_spec__0(v_t_2964_, v_snd_2971_, v___x_2975_, v___x_2976_);
lean_dec(v_snd_2971_);
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_propagatesRhsStickiness___boxed(lean_object* v_env_2978_, lean_object* v_t_2979_){
_start:
{
uint8_t v_res_2980_; lean_object* v_r_2981_; 
v_res_2980_ = l_Lean_Fmt_propagatesRhsStickiness(v_env_2978_, v_t_2979_);
v_r_2981_ = lean_box(v_res_2980_);
return v_r_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(uint8_t v_x_2982_){
_start:
{
switch(v_x_2982_)
{
case 0:
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_unsigned_to_nat(0u);
return v___x_2983_;
}
case 1:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_unsigned_to_nat(1u);
return v___x_2984_;
}
default: 
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_unsigned_to_nat(2u);
return v___x_2985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorIdx___boxed(lean_object* v_x_2986_){
_start:
{
uint8_t v_x_boxed_2987_; lean_object* v_res_2988_; 
v_x_boxed_2987_ = lean_unbox(v_x_2986_);
v_res_2988_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(v_x_boxed_2987_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(lean_object* v_k_2989_){
_start:
{
lean_inc(v_k_2989_);
return v_k_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg___boxed(lean_object* v_k_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim___redArg(v_k_2990_);
lean_dec(v_k_2990_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim(lean_object* v_motive_2992_, lean_object* v_ctorIdx_2993_, uint8_t v_t_2994_, lean_object* v_h_2995_, lean_object* v_k_2996_){
_start:
{
lean_inc(v_k_2996_);
return v_k_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_ctorElim___boxed(lean_object* v_motive_2997_, lean_object* v_ctorIdx_2998_, lean_object* v_t_2999_, lean_object* v_h_3000_, lean_object* v_k_3001_){
_start:
{
uint8_t v_t_boxed_3002_; lean_object* v_res_3003_; 
v_t_boxed_3002_ = lean_unbox(v_t_2999_);
v_res_3003_ = l_Lean_Fmt_InfixOperationAssociativity_ctorElim(v_motive_2997_, v_ctorIdx_2998_, v_t_boxed_3002_, v_h_3000_, v_k_3001_);
lean_dec(v_k_3001_);
lean_dec(v_ctorIdx_2998_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(lean_object* v_left_3004_){
_start:
{
lean_inc(v_left_3004_);
return v_left_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg___boxed(lean_object* v_left_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim___redArg(v_left_3005_);
lean_dec(v_left_3005_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim(lean_object* v_motive_3007_, uint8_t v_t_3008_, lean_object* v_h_3009_, lean_object* v_left_3010_){
_start:
{
lean_inc(v_left_3010_);
return v_left_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_left_elim___boxed(lean_object* v_motive_3011_, lean_object* v_t_3012_, lean_object* v_h_3013_, lean_object* v_left_3014_){
_start:
{
uint8_t v_t_boxed_3015_; lean_object* v_res_3016_; 
v_t_boxed_3015_ = lean_unbox(v_t_3012_);
v_res_3016_ = l_Lean_Fmt_InfixOperationAssociativity_left_elim(v_motive_3011_, v_t_boxed_3015_, v_h_3013_, v_left_3014_);
lean_dec(v_left_3014_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(lean_object* v_right_3017_){
_start:
{
lean_inc(v_right_3017_);
return v_right_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg___boxed(lean_object* v_right_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim___redArg(v_right_3018_);
lean_dec(v_right_3018_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim(lean_object* v_motive_3020_, uint8_t v_t_3021_, lean_object* v_h_3022_, lean_object* v_right_3023_){
_start:
{
lean_inc(v_right_3023_);
return v_right_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_right_elim___boxed(lean_object* v_motive_3024_, lean_object* v_t_3025_, lean_object* v_h_3026_, lean_object* v_right_3027_){
_start:
{
uint8_t v_t_boxed_3028_; lean_object* v_res_3029_; 
v_t_boxed_3028_ = lean_unbox(v_t_3025_);
v_res_3029_ = l_Lean_Fmt_InfixOperationAssociativity_right_elim(v_motive_3024_, v_t_boxed_3028_, v_h_3026_, v_right_3027_);
lean_dec(v_right_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(lean_object* v_middle_3030_){
_start:
{
lean_inc(v_middle_3030_);
return v_middle_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg___boxed(lean_object* v_middle_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim___redArg(v_middle_3031_);
lean_dec(v_middle_3031_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim(lean_object* v_motive_3033_, uint8_t v_t_3034_, lean_object* v_h_3035_, lean_object* v_middle_3036_){
_start:
{
lean_inc(v_middle_3036_);
return v_middle_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_InfixOperationAssociativity_middle_elim___boxed(lean_object* v_motive_3037_, lean_object* v_t_3038_, lean_object* v_h_3039_, lean_object* v_middle_3040_){
_start:
{
uint8_t v_t_boxed_3041_; lean_object* v_res_3042_; 
v_t_boxed_3041_ = lean_unbox(v_t_3038_);
v_res_3042_ = l_Lean_Fmt_InfixOperationAssociativity_middle_elim(v_motive_3037_, v_t_boxed_3041_, v_h_3039_, v_middle_3040_);
lean_dec(v_middle_3040_);
return v_res_3042_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default(void){
_start:
{
uint8_t v___x_3043_; 
v___x_3043_ = 0;
return v___x_3043_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity(void){
_start:
{
uint8_t v___x_3044_; 
v___x_3044_ = 0;
return v___x_3044_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(uint8_t v_x_3045_, uint8_t v_y_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3047_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(v_x_3045_);
v___x_3048_ = l_Lean_Fmt_InfixOperationAssociativity_ctorIdx(v_y_3046_);
v___x_3049_ = lean_nat_dec_eq(v___x_3047_, v___x_3048_);
lean_dec(v___x_3048_);
lean_dec(v___x_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationAssociativity_beq___boxed(lean_object* v_x_3050_, lean_object* v_y_3051_){
_start:
{
uint8_t v_x_21__boxed_3052_; uint8_t v_y_22__boxed_3053_; uint8_t v_res_3054_; lean_object* v_r_3055_; 
v_x_21__boxed_3052_ = lean_unbox(v_x_3050_);
v_y_22__boxed_3053_ = lean_unbox(v_y_3051_);
v_res_3054_ = l_Lean_Fmt_instBEqInfixOperationAssociativity_beq(v_x_21__boxed_3052_, v_y_22__boxed_3053_);
v_r_3055_ = lean_box(v_res_3054_);
return v_r_3055_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object* v_x_3062_, lean_object* v_x_3063_){
_start:
{
lean_object* v_prec_3064_; lean_object* v_lhsPrec_3065_; lean_object* v_rhsPrec_3066_; lean_object* v_prec_3067_; lean_object* v_lhsPrec_3068_; lean_object* v_rhsPrec_3069_; uint8_t v___x_3070_; 
v_prec_3064_ = lean_ctor_get(v_x_3062_, 0);
v_lhsPrec_3065_ = lean_ctor_get(v_x_3062_, 1);
v_rhsPrec_3066_ = lean_ctor_get(v_x_3062_, 2);
v_prec_3067_ = lean_ctor_get(v_x_3063_, 0);
v_lhsPrec_3068_ = lean_ctor_get(v_x_3063_, 1);
v_rhsPrec_3069_ = lean_ctor_get(v_x_3063_, 2);
v___x_3070_ = lean_nat_dec_eq(v_prec_3064_, v_prec_3067_);
if (v___x_3070_ == 0)
{
return v___x_3070_;
}
else
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_nat_dec_eq(v_lhsPrec_3065_, v_lhsPrec_3068_);
if (v___x_3071_ == 0)
{
return v___x_3071_;
}
else
{
uint8_t v___x_3072_; 
v___x_3072_ = lean_nat_dec_eq(v_rhsPrec_3066_, v_rhsPrec_3069_);
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperationPrecs_beq___boxed(lean_object* v_x_3073_, lean_object* v_x_3074_){
_start:
{
uint8_t v_res_3075_; lean_object* v_r_3076_; 
v_res_3075_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_x_3073_, v_x_3074_);
lean_dec_ref(v_x_3074_);
lean_dec_ref(v_x_3073_);
v_r_3076_ = lean_box(v_res_3075_);
return v_r_3076_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_unsigned_to_nat(16u);
v___x_3081_ = lean_mk_array(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__0);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set(v___x_3084_, 1, v___x_3082_);
return v___x_3084_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; lean_object* v___x_3088_; 
v___x_3085_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__1);
v___x_3086_ = lean_box(0);
v___x_3087_ = 0;
v___x_3088_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_3088_, 0, v___x_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_3085_);
lean_ctor_set_uint8(v___x_3088_, sizeof(void*)*2, v___x_3087_);
lean_ctor_set_uint8(v___x_3088_, sizeof(void*)*2 + 1, v___x_3087_);
return v___x_3088_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation_default(void){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_obj_once(&l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2, &l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2_once, _init_l_Lean_Fmt_instInhabitedInfixOperation_default___closed__2);
return v___x_3089_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedInfixOperation(void){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Fmt_instInhabitedInfixOperation_default;
return v___x_3090_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
if (lean_obj_tag(v_x_3091_) == 0)
{
if (lean_obj_tag(v_x_3092_) == 0)
{
uint8_t v___x_3093_; 
v___x_3093_ = 1;
return v___x_3093_;
}
else
{
uint8_t v___x_3094_; 
v___x_3094_ = 0;
return v___x_3094_;
}
}
else
{
if (lean_obj_tag(v_x_3092_) == 0)
{
uint8_t v___x_3095_; 
v___x_3095_ = 0;
return v___x_3095_;
}
else
{
lean_object* v_val_3096_; lean_object* v_val_3097_; uint8_t v___x_3098_; 
v_val_3096_ = lean_ctor_get(v_x_3091_, 0);
v_val_3097_ = lean_ctor_get(v_x_3092_, 0);
v___x_3098_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_3096_, v_val_3097_);
return v___x_3098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0___boxed(lean_object* v_x_3099_, lean_object* v_x_3100_){
_start:
{
uint8_t v_res_3101_; lean_object* v_r_3102_; 
v_res_3101_ = l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_x_3099_, v_x_3100_);
lean_dec(v_x_3100_);
lean_dec(v_x_3099_);
v_r_3102_ = lean_box(v_res_3101_);
return v_r_3102_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_x_3103_, lean_object* v_x_3104_){
_start:
{
if (lean_obj_tag(v_x_3103_) == 0)
{
if (lean_obj_tag(v_x_3104_) == 0)
{
uint8_t v___x_3105_; 
v___x_3105_ = 1;
return v___x_3105_;
}
else
{
uint8_t v___x_3106_; 
v___x_3106_ = 0;
return v___x_3106_;
}
}
else
{
if (lean_obj_tag(v_x_3104_) == 0)
{
uint8_t v___x_3107_; 
v___x_3107_ = 0;
return v___x_3107_;
}
else
{
uint8_t v___x_3108_; 
v___x_3108_ = 1;
return v___x_3108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_x_3109_, lean_object* v_x_3110_){
_start:
{
uint8_t v_res_3111_; lean_object* v_r_3112_; 
v_res_3111_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v_x_3109_, v_x_3110_);
lean_dec(v_x_3110_);
lean_dec(v_x_3109_);
v_r_3112_ = lean_box(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_m_u2082_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; uint8_t v___y_3124_; uint8_t v___x_3137_; 
v___x_3121_ = lean_box(0);
v___x_3122_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v___x_3137_ = lean_nat_dec_eq(v___x_3117_, v___x_3118_);
if (v___x_3137_ == 0)
{
uint8_t v___x_3138_; 
v___x_3138_ = 1;
v___y_3124_ = v___x_3138_;
goto v___jp_3123_;
}
else
{
uint8_t v___x_3139_; 
v___x_3139_ = 0;
v___y_3124_ = v___x_3139_;
goto v___jp_3123_;
}
v___jp_3123_:
{
if (lean_obj_tag(v_a_3119_) == 0)
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_a_3120_);
return v___x_3125_;
}
else
{
lean_object* v_key_3126_; lean_object* v_value_3127_; lean_object* v_tail_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
lean_dec_ref(v_a_3120_);
v_key_3126_ = lean_ctor_get(v_a_3119_, 0);
v_value_3127_ = lean_ctor_get(v_a_3119_, 1);
v_tail_3128_ = lean_ctor_get(v_a_3119_, 2);
v___x_3129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_evalFmtAttributeKey_spec__0_spec__2___redArg(v_m_u2082_3116_, v_key_3126_);
lean_inc(v_value_3127_);
v___x_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_value_3127_);
v___x_3131_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__4(v___x_3129_, v___x_3130_);
lean_dec_ref_known(v___x_3130_, 1);
lean_dec(v___x_3129_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3132_ = lean_box(v___y_3124_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3121_);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
else
{
v_a_3119_ = v_tail_3128_;
v_a_3120_ = v___x_3122_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_m_u2082_3140_, lean_object* v___x_3141_, lean_object* v___x_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3140_, v___x_3141_, v___x_3142_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3143_);
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
lean_dec_ref(v_m_u2082_3140_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(lean_object* v_m_u2082_3146_, lean_object* v___x_3147_, lean_object* v___x_3148_, lean_object* v_as_3149_, size_t v_sz_3150_, size_t v_i_3151_, lean_object* v_b_3152_){
_start:
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_usize_dec_lt(v_i_3151_, v_sz_3150_);
if (v___x_3153_ == 0)
{
return v_b_3152_;
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3155_; 
v_a_3154_ = lean_array_uget_borrowed(v_as_3149_, v_i_3151_);
v___x_3155_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5(v_m_u2082_3146_, v___x_3147_, v___x_3148_, v_a_3154_, v_b_3152_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
return v_a_3156_;
}
else
{
lean_object* v_a_3157_; size_t v___x_3158_; size_t v___x_3159_; 
v_a_3157_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___x_3155_, 1);
v___x_3158_ = ((size_t)1ULL);
v___x_3159_ = lean_usize_add(v_i_3151_, v___x_3158_);
v_i_3151_ = v___x_3159_;
v_b_3152_ = v_a_3157_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_m_u2082_3161_, lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_as_3164_, lean_object* v_sz_3165_, lean_object* v_i_3166_, lean_object* v_b_3167_){
_start:
{
size_t v_sz_boxed_3168_; size_t v_i_boxed_3169_; lean_object* v_res_3170_; 
v_sz_boxed_3168_ = lean_unbox_usize(v_sz_3165_);
lean_dec(v_sz_3165_);
v_i_boxed_3169_ = lean_unbox_usize(v_i_3166_);
lean_dec(v_i_3166_);
v_res_3170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3161_, v___x_3162_, v___x_3163_, v_as_3164_, v_sz_boxed_3168_, v_i_boxed_3169_, v_b_3167_);
lean_dec_ref(v_as_3164_);
lean_dec(v___x_3163_);
lean_dec(v___x_3162_);
lean_dec_ref(v_m_u2082_3161_);
return v_res_3170_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(lean_object* v_m_u2081_3171_, lean_object* v_m_u2082_3172_){
_start:
{
lean_object* v_size_3173_; lean_object* v_buckets_3174_; lean_object* v_size_3175_; uint8_t v___x_3176_; 
v_size_3173_ = lean_ctor_get(v_m_u2081_3171_, 0);
v_buckets_3174_ = lean_ctor_get(v_m_u2081_3171_, 1);
v_size_3175_ = lean_ctor_get(v_m_u2082_3172_, 0);
v___x_3176_ = lean_nat_dec_eq(v_size_3173_, v_size_3175_);
if (v___x_3176_ == 0)
{
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; size_t v_sz_3178_; size_t v___x_3179_; lean_object* v___x_3180_; lean_object* v_fst_3181_; 
v___x_3177_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__5___closed__0));
v_sz_3178_ = lean_array_size(v_buckets_3174_);
v___x_3179_ = ((size_t)0ULL);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3_spec__6(v_m_u2082_3172_, v_size_3173_, v_size_3175_, v_buckets_3174_, v_sz_3178_, v___x_3179_, v___x_3177_);
v_fst_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_fst_3181_);
lean_dec_ref(v___x_3180_);
if (lean_obj_tag(v_fst_3181_) == 0)
{
return v___x_3176_;
}
else
{
lean_object* v_val_3182_; uint8_t v___x_3183_; 
v_val_3182_ = lean_ctor_get(v_fst_3181_, 0);
lean_inc(v_val_3182_);
lean_dec_ref_known(v_fst_3181_, 1);
v___x_3183_ = lean_unbox(v_val_3182_);
lean_dec(v_val_3182_);
return v___x_3183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_m_u2081_3184_, lean_object* v_m_u2082_3185_){
_start:
{
uint8_t v_res_3186_; lean_object* v_r_3187_; 
v_res_3186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3184_, v_m_u2082_3185_);
lean_dec_ref(v_m_u2082_3185_);
lean_dec_ref(v_m_u2081_3184_);
v_r_3187_ = lean_box(v_res_3186_);
return v_r_3187_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(lean_object* v_m_u2081_3188_, lean_object* v_m_u2082_3189_){
_start:
{
uint8_t v___x_3190_; 
v___x_3190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3188_, v_m_u2082_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2___boxed(lean_object* v_m_u2081_3191_, lean_object* v_m_u2082_3192_){
_start:
{
uint8_t v_res_3193_; lean_object* v_r_3194_; 
v_res_3193_ = l_Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2(v_m_u2081_3191_, v_m_u2082_3192_);
lean_dec_ref(v_m_u2082_3192_);
lean_dec_ref(v_m_u2081_3191_);
v_r_3194_ = lean_box(v_res_3193_);
return v_r_3194_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(lean_object* v_m_u2081_3195_, lean_object* v_m_u2082_3196_){
_start:
{
uint8_t v___x_3197_; 
v___x_3197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3195_, v_m_u2082_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1___boxed(lean_object* v_m_u2081_3198_, lean_object* v_m_u2082_3199_){
_start:
{
uint8_t v_res_3200_; lean_object* v_r_3201_; 
v_res_3200_ = l_Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1(v_m_u2081_3198_, v_m_u2082_3199_);
lean_dec_ref(v_m_u2082_3199_);
lean_dec_ref(v_m_u2081_3198_);
v_r_3201_ = lean_box(v_res_3200_);
return v_r_3201_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(lean_object* v_m_u2081_3202_, lean_object* v_m_u2082_3203_){
_start:
{
uint8_t v___x_3204_; 
v___x_3204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_m_u2081_3202_, v_m_u2082_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1___boxed(lean_object* v_m_u2081_3205_, lean_object* v_m_u2082_3206_){
_start:
{
uint8_t v_res_3207_; lean_object* v_r_3208_; 
v_res_3207_ = l_Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1(v_m_u2081_3205_, v_m_u2082_3206_);
lean_dec_ref(v_m_u2082_3206_);
lean_dec_ref(v_m_u2081_3205_);
v_r_3208_ = lean_box(v_res_3207_);
return v_r_3208_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqInfixOperation_beq(lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
uint8_t v_sparse_3211_; uint8_t v_separateFinalOperand_3212_; lean_object* v_precs_x3f_3213_; lean_object* v_extendedChainKinds_3214_; uint8_t v_sparse_3215_; uint8_t v_separateFinalOperand_3216_; lean_object* v_precs_x3f_3217_; lean_object* v_extendedChainKinds_3218_; 
v_sparse_3211_ = lean_ctor_get_uint8(v_x_3209_, sizeof(void*)*2);
v_separateFinalOperand_3212_ = lean_ctor_get_uint8(v_x_3209_, sizeof(void*)*2 + 1);
v_precs_x3f_3213_ = lean_ctor_get(v_x_3209_, 0);
v_extendedChainKinds_3214_ = lean_ctor_get(v_x_3209_, 1);
v_sparse_3215_ = lean_ctor_get_uint8(v_x_3210_, sizeof(void*)*2);
v_separateFinalOperand_3216_ = lean_ctor_get_uint8(v_x_3210_, sizeof(void*)*2 + 1);
v_precs_x3f_3217_ = lean_ctor_get(v_x_3210_, 0);
v_extendedChainKinds_3218_ = lean_ctor_get(v_x_3210_, 1);
if (v_sparse_3215_ == 0)
{
if (v_sparse_3211_ == 0)
{
goto v___jp_3222_;
}
else
{
return v_sparse_3215_;
}
}
else
{
if (v_sparse_3211_ == 0)
{
return v_sparse_3211_;
}
else
{
goto v___jp_3222_;
}
}
v___jp_3219_:
{
uint8_t v___x_3220_; 
v___x_3220_ = l_Option_instBEq_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__0(v_precs_x3f_3213_, v_precs_x3f_3217_);
if (v___x_3220_ == 0)
{
return v___x_3220_;
}
else
{
uint8_t v___x_3221_; 
v___x_3221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___at___00Std_DHashMap_Const_beq___at___00Std_HashMap_beq___at___00Std_HashSet_beq___at___00Lean_Fmt_instBEqInfixOperation_beq_spec__1_spec__1_spec__2_spec__3(v_extendedChainKinds_3214_, v_extendedChainKinds_3218_);
return v___x_3221_;
}
}
v___jp_3222_:
{
if (v_separateFinalOperand_3216_ == 0)
{
if (v_separateFinalOperand_3212_ == 0)
{
goto v___jp_3219_;
}
else
{
return v_separateFinalOperand_3216_;
}
}
else
{
if (v_separateFinalOperand_3212_ == 0)
{
return v_separateFinalOperand_3212_;
}
else
{
goto v___jp_3219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqInfixOperation_beq___boxed(lean_object* v_x_3223_, lean_object* v_x_3224_){
_start:
{
uint8_t v_res_3225_; lean_object* v_r_3226_; 
v_res_3225_ = l_Lean_Fmt_instBEqInfixOperation_beq(v_x_3223_, v_x_3224_);
lean_dec_ref(v_x_3224_);
lean_dec_ref(v_x_3223_);
v_r_3226_ = lean_box(v_res_3225_);
return v_r_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_));
v___x_3258_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_));
v___x_3259_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3257_, v___x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2____boxed(lean_object* v_a_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_();
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_));
v___x_3291_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_));
v___x_3292_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3290_, v___x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2____boxed(lean_object* v_a_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_();
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx(lean_object* v_x_3295_){
_start:
{
if (lean_obj_tag(v_x_3295_) == 0)
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_unsigned_to_nat(0u);
return v___x_3296_;
}
else
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_unsigned_to_nat(1u);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorIdx___boxed(lean_object* v_x_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Fmt_QuantifierBinders_ctorIdx(v_x_3298_);
lean_dec_ref(v_x_3298_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(lean_object* v_t_3300_, lean_object* v_k_3301_){
_start:
{
if (lean_obj_tag(v_t_3300_) == 0)
{
lean_object* v_group_3302_; lean_object* v___x_3303_; 
v_group_3302_ = lean_ctor_get(v_t_3300_, 0);
lean_inc_ref(v_group_3302_);
lean_dec_ref_known(v_t_3300_, 1);
v___x_3303_ = lean_apply_1(v_k_3301_, v_group_3302_);
return v___x_3303_;
}
else
{
lean_object* v_lhs_3304_; lean_object* v_rhs_3305_; lean_object* v___x_3306_; 
v_lhs_3304_ = lean_ctor_get(v_t_3300_, 0);
lean_inc(v_lhs_3304_);
v_rhs_3305_ = lean_ctor_get(v_t_3300_, 1);
lean_inc(v_rhs_3305_);
lean_dec_ref_known(v_t_3300_, 2);
v___x_3306_ = lean_apply_2(v_k_3301_, v_lhs_3304_, v_rhs_3305_);
return v___x_3306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim(lean_object* v_motive_3307_, lean_object* v_ctorIdx_3308_, lean_object* v_t_3309_, lean_object* v_h_3310_, lean_object* v_k_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3309_, v_k_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_ctorElim___boxed(lean_object* v_motive_3313_, lean_object* v_ctorIdx_3314_, lean_object* v_t_3315_, lean_object* v_h_3316_, lean_object* v_k_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Fmt_QuantifierBinders_ctorElim(v_motive_3313_, v_ctorIdx_3314_, v_t_3315_, v_h_3316_, v_k_3317_);
lean_dec(v_ctorIdx_3314_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim___redArg(lean_object* v_t_3319_, lean_object* v_binders_3320_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3319_, v_binders_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_binders_elim(lean_object* v_motive_3322_, lean_object* v_t_3323_, lean_object* v_h_3324_, lean_object* v_binders_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3323_, v_binders_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim___redArg(lean_object* v_t_3327_, lean_object* v_pred_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3327_, v_pred_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_QuantifierBinders_pred_elim(lean_object* v_motive_3330_, lean_object* v_t_3331_, lean_object* v_h_3332_, lean_object* v_pred_3333_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_Fmt_QuantifierBinders_ctorElim___redArg(v_t_3331_, v_pred_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__8_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_));
v___x_3364_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn___closed__10_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_));
v___x_3365_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3363_, v___x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2____boxed(lean_object* v_a_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_();
return v_res_3367_;
}
}
lean_object* runtime_initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ShareCommon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_Module(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_LineInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_instInhabitedRangeKind_default = _init_l_Lean_Fmt_instInhabitedRangeKind_default();
l_Lean_Fmt_instInhabitedRangeKind = _init_l_Lean_Fmt_instInhabitedRangeKind();
l_Lean_Fmt_instInhabitedBacktrackableState_default = _init_l_Lean_Fmt_instInhabitedBacktrackableState_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedBacktrackableState_default);
l_Lean_Fmt_instInhabitedBacktrackableState = _init_l_Lean_Fmt_instInhabitedBacktrackableState();
lean_mark_persistent(l_Lean_Fmt_instInhabitedBacktrackableState);
l_Lean_Fmt_instInhabitedState_default = _init_l_Lean_Fmt_instInhabitedState_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedState_default);
l_Lean_Fmt_instInhabitedState = _init_l_Lean_Fmt_instInhabitedState();
lean_mark_persistent(l_Lean_Fmt_instInhabitedState);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4196091313____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinFmtProvidersRef);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_655907140____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_fmtProvidersExt);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3390004911____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4242651859____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinCommentCollectorsRef);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_4223495705____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_commentCollectorsExt);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_650409495____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2623710346____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Fmt_fmtAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Fmt_fmtAttribute);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1541401052____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_builtinStickyTermFnsRef);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3864189901____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_stickyTermFnsExt);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_2308933963____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default = _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity_default();
l_Lean_Fmt_instInhabitedInfixOperationAssociativity = _init_l_Lean_Fmt_instInhabitedInfixOperationAssociativity();
l_Lean_Fmt_instInhabitedInfixOperation_default = _init_l_Lean_Fmt_instInhabitedInfixOperation_default();
lean_mark_persistent(l_Lean_Fmt_instInhabitedInfixOperation_default);
l_Lean_Fmt_instInhabitedInfixOperation = _init_l_Lean_Fmt_instInhabitedInfixOperation();
lean_mark_persistent(l_Lean_Fmt_instInhabitedInfixOperation);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_1852599800____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Fmt_infixFmtAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Fmt_infixFmtAttribute);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3281337357____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Fmt_conditionalFmtAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Fmt_conditionalFmtAttribute);
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Attribute_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Attribute_3956166579____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Fmt_quantifierFmtAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Fmt_quantifierFmtAttribute);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_LineInfo(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_Module(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Core_Formatter(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_LineInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Core_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Attribute(builtin);
}
#ifdef __cplusplus
}
#endif

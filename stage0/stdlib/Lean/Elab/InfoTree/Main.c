// Lean compiler output
// Module: Lean.Elab.InfoTree.Main
// Imports: public import Lean.Elab.InfoTree.Basic public import Lean.Meta.PPGoal public import Lean.ReservedNameAction import Init.Data.Format.Macro
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_CompletionInfo_stx(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_instReprDocElabKind_repr(uint8_t, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_Std_Format_nestD(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CustomInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[CustomInfo("};
static const lean_object* l_Lean_Elab_CustomInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_CustomInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CustomInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CustomInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_CustomInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_CustomInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_CustomInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")]"};
static const lean_object* l_Lean_Elab_CustomInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_CustomInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CustomInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CustomInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_CustomInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_CustomInfo_format___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CustomInfo_format(lean_object*);
static const lean_closure_object l_Lean_Elab_instToFormatCustomInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_CustomInfo_format, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_instToFormatCustomInfo___closed__0 = (const lean_object*)&l_Lean_Elab_instToFormatCustomInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instToFormatCustomInfo = (const lean_object*)&l_Lean_Elab_instToFormatCustomInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6;
static const lean_ctor_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9;
static const lean_array_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13_value;
static const lean_string_object l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "<InfoTree>"};
static const lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2;
static const lean_array_object l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "†"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__6_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "†!"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " @ "};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_TermInfo_format___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "[Term] "};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_TermInfo_format___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_TermInfo_format___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__6_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "(isBinder := true) "};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_TermInfo_format___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "<failed-to-infer-type>"};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_TermInfo_format___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__8_value)}};
static const lean_object* l_Lean_Elab_TermInfo_format___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_TermInfo_format___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_PartialTermInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "[PartialTerm] @ "};
static const lean_object* l_Lean_Elab_PartialTermInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_PartialTermInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_PartialTermInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialTermInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_PartialTermInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_PartialTermInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0 = (const lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value;
static const lean_ctor_object l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__0_value)}};
static const lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1 = (const lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1_value;
static const lean_string_object l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2 = (const lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value;
static const lean_ctor_object l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__2_value)}};
static const lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3 = (const lean_object*)&l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object*);
static const lean_string_object l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "[Completion-Id] "};
static const lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CompletionInfo_format___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CompletionInfo_format___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CompletionInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "[Completion-Dot] "};
static const lean_object* l_Lean_Elab_CompletionInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CompletionInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_CompletionInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_CompletionInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "[Completion] "};
static const lean_object* l_Lean_Elab_CompletionInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_CompletionInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_CompletionInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_CompletionInfo_format___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_CommandInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[Command] @ "};
static const lean_object* l_Lean_Elab_CommandInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_CommandInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_CommandInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_CommandInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_CommandInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_CommandInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OptionInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "[Option] "};
static const lean_object* l_Lean_Elab_OptionInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_OptionInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_OptionInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_OptionInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_OptionInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_OptionInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ErrorNameInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[ErrorName] "};
static const lean_object* l_Lean_Elab_ErrorNameInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_ErrorNameInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ErrorNameInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorNameInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_ErrorNameInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_ErrorNameInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "[Field] "};
static const lean_object* l_Lean_Elab_FieldInfo_format___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_FieldInfo_format___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_FieldInfo_format___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Elab_FieldInfo_format___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_FieldInfo_format___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_FieldInfo_format___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_FieldInfo_format___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__0;
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__1;
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__2;
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__3;
static lean_once_cell_t l_Lean_Elab_ContextInfo_ppGoals___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__4;
static const lean_string_object l_Lean_Elab_ContextInfo_ppGoals___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no goals"};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__5 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ContextInfo_ppGoals___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__5_value)}};
static const lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__6 = (const lean_object*)&l_Lean_Elab_ContextInfo_ppGoals___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TacticInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[Tactic] @ "};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_TacticInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TacticInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_TacticInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nbefore "};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_TacticInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TacticInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_TacticInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nafter "};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_TacticInfo_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TacticInfo_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_TacticInfo_format___closed__5 = (const lean_object*)&l_Lean_Elab_TacticInfo_format___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_MacroExpansionInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "[MacroExpansion]\n"};
static const lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_MacroExpansionInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_MacroExpansionInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\n===>\n"};
static const lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_MacroExpansionInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_MacroExpansionInfo_format___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_UserWidgetInfo_format___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__0;
static lean_once_cell_t l_Lean_Elab_UserWidgetInfo_format___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__1;
static lean_once_cell_t l_Lean_Elab_UserWidgetInfo_format___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__2;
static const lean_string_object l_Lean_Elab_UserWidgetInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "[UserWidget] "};
static const lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__3_value;
static const lean_ctor_object l_Lean_Elab_UserWidgetInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__3_value)}};
static const lean_object* l_Lean_Elab_UserWidgetInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_UserWidgetInfo_format___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object*);
static const lean_string_object l_Lean_Elab_FVarAliasInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[FVarAlias] "};
static const lean_object* l_Lean_Elab_FVarAliasInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_FVarAliasInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_FVarAliasInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_FVarAliasInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -> "};
static const lean_object* l_Lean_Elab_FVarAliasInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_FVarAliasInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_FVarAliasInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_FVarAliasInfo_format___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object*);
static const lean_string_object l_Lean_Elab_FieldRedeclInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "[FieldRedecl] @ "};
static const lean_object* l_Lean_Elab_FieldRedeclInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_FieldRedeclInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_FieldRedeclInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_FieldRedeclInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_FieldRedeclInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_FieldRedeclInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "[Error: "};
static const lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "[DelabTerm] @ "};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DelabTermInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\nLocation: "};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_DelabTermInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\nDocstring: "};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_DelabTermInfo_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__5 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__5_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\nExplicit: "};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__6 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__6_value;
static const lean_ctor_object l_Lean_Elab_DelabTermInfo_format___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__6_value)}};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__7 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__7_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__8 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__8_value;
static const lean_string_object l_Lean_Elab_DelabTermInfo_format___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_DelabTermInfo_format___closed__9 = (const lean_object*)&l_Lean_Elab_DelabTermInfo_format___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ChoiceInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[Choice] @ "};
static const lean_object* l_Lean_Elab_ChoiceInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_ChoiceInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ChoiceInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_ChoiceInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_ChoiceInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "[ChoiceResolution] alternative "};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__5 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__5_value;
static const lean_string_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ") @ "};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__6 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ChoiceResolutionInfo_format___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__6_value)}};
static const lean_object* l_Lean_Elab_ChoiceResolutionInfo_format___closed__7 = (const lean_object*)&l_Lean_Elab_ChoiceResolutionInfo_format___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DocInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[Doc] "};
static const lean_object* l_Lean_Elab_DocInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_DocInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DocInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DocInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_DocInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_DocInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DocElabInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "[DocElab] "};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_DocElabInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_DocElabInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_DocElabInfo_format___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_PartialContextInfo_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__0 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_PartialContextInfo_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__1 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__1_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parent["};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__2 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__2_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "autoImplicits["};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__3 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__3_value;
static const lean_string_object l_Lean_Elab_PartialContextInfo_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Elab_PartialContextInfo_format___closed__4 = (const lean_object*)&l_Lean_Elab_PartialContextInfo_format___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object*);
static const lean_string_object l_Lean_Elab_InfoTree_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 25, .m_data = "• <context-not-available>"};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__0_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_format___closed__0_value)}};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__1_value;
static const lean_string_object l_Lean_Elab_InfoTree_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__2 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__2_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_format___closed__2_value)}};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__3 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__3_value;
static const lean_string_object l_Lean_Elab_InfoTree_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = "• \?"};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__4 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__4_value;
static const lean_ctor_object l_Lean_Elab_InfoTree_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_format___closed__4_value)}};
static const lean_object* l_Lean_Elab_InfoTree_format___closed__5 = (const lean_object*)&l_Lean_Elab_InfoTree_format___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_getResetInfoTrees___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_getResetInfoTrees___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getResetInfoTrees___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_getResetInfoTrees___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withInfoContext_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withInfoContext_x27___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withInfoContext_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqMVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableMVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Main"};
static const lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Elab.assignInfoHoleId"};
static const lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "assertion violation: ( __do_lift._@.Lean.Elab.InfoTree.Main.2379084842._hygCtx._hyg.19.0 ).isNone\n  "};
static const lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withEnableInfoTree___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withEnableInfoTree___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withEnableInfoTree___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__0(lean_object* v_____do__lift_1_, lean_object* v_____do__lift_2_, lean_object* v_____do__lift_3_, lean_object* v_____do__lift_4_, lean_object* v_____do__lift_5_, lean_object* v_toPure_6_, lean_object* v_____do__lift_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_8_ = lean_box(0);
v___x_9_ = l_Lean_instInhabitedFileMap_default;
v___x_10_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_10_, 0, v_____do__lift_1_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_9_);
lean_ctor_set(v___x_10_, 3, v_____do__lift_2_);
lean_ctor_set(v___x_10_, 4, v_____do__lift_3_);
lean_ctor_set(v___x_10_, 5, v_____do__lift_4_);
lean_ctor_set(v___x_10_, 6, v_____do__lift_5_);
lean_ctor_set(v___x_10_, 7, v_____do__lift_7_);
v___x_11_ = lean_apply_2(v_toPure_6_, lean_box(0), v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__1(lean_object* v_inst_12_, lean_object* v_____do__lift_13_, lean_object* v_____do__lift_14_, lean_object* v_____do__lift_15_, lean_object* v_____do__lift_16_, lean_object* v_toPure_17_, lean_object* v_toBind_18_, lean_object* v_____do__lift_19_){
_start:
{
lean_object* v_getNGen_20_; lean_object* v___f_21_; lean_object* v___x_22_; 
v_getNGen_20_ = lean_ctor_get(v_inst_12_, 0);
lean_inc(v_getNGen_20_);
lean_dec_ref(v_inst_12_);
v___f_21_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__0), 7, 6);
lean_closure_set(v___f_21_, 0, v_____do__lift_13_);
lean_closure_set(v___f_21_, 1, v_____do__lift_14_);
lean_closure_set(v___f_21_, 2, v_____do__lift_15_);
lean_closure_set(v___f_21_, 3, v_____do__lift_16_);
lean_closure_set(v___f_21_, 4, v_____do__lift_19_);
lean_closure_set(v___f_21_, 5, v_toPure_17_);
v___x_22_ = lean_apply_4(v_toBind_18_, lean_box(0), lean_box(0), v_getNGen_20_, v___f_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__2(lean_object* v_inst_23_, lean_object* v_____do__lift_24_, lean_object* v_____do__lift_25_, lean_object* v_____do__lift_26_, lean_object* v_toPure_27_, lean_object* v_toBind_28_, lean_object* v_getOpenDecls_29_, lean_object* v_____do__lift_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; 
lean_inc(v_toBind_28_);
v___f_31_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__1), 8, 7);
lean_closure_set(v___f_31_, 0, v_inst_23_);
lean_closure_set(v___f_31_, 1, v_____do__lift_24_);
lean_closure_set(v___f_31_, 2, v_____do__lift_25_);
lean_closure_set(v___f_31_, 3, v_____do__lift_26_);
lean_closure_set(v___f_31_, 4, v_____do__lift_30_);
lean_closure_set(v___f_31_, 5, v_toPure_27_);
lean_closure_set(v___f_31_, 6, v_toBind_28_);
v___x_32_ = lean_apply_4(v_toBind_28_, lean_box(0), lean_box(0), v_getOpenDecls_29_, v___f_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_____do__lift_35_, lean_object* v_____do__lift_36_, lean_object* v_toPure_37_, lean_object* v_toBind_38_, lean_object* v_____do__lift_39_){
_start:
{
lean_object* v_getCurrNamespace_40_; lean_object* v_getOpenDecls_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v_getCurrNamespace_40_ = lean_ctor_get(v_inst_33_, 0);
lean_inc(v_getCurrNamespace_40_);
v_getOpenDecls_41_ = lean_ctor_get(v_inst_33_, 1);
lean_inc(v_getOpenDecls_41_);
lean_dec_ref(v_inst_33_);
lean_inc(v_toBind_38_);
v___f_42_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__2), 8, 7);
lean_closure_set(v___f_42_, 0, v_inst_34_);
lean_closure_set(v___f_42_, 1, v_____do__lift_35_);
lean_closure_set(v___f_42_, 2, v_____do__lift_36_);
lean_closure_set(v___f_42_, 3, v_____do__lift_39_);
lean_closure_set(v___f_42_, 4, v_toPure_37_);
lean_closure_set(v___f_42_, 5, v_toBind_38_);
lean_closure_set(v___f_42_, 6, v_getOpenDecls_41_);
v___x_43_ = lean_apply_4(v_toBind_38_, lean_box(0), lean_box(0), v_getCurrNamespace_40_, v___f_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_____do__lift_46_, lean_object* v_toPure_47_, lean_object* v_toBind_48_, lean_object* v_inst_49_, lean_object* v_____do__lift_50_){
_start:
{
lean_object* v___f_51_; lean_object* v___x_52_; 
lean_inc(v_toBind_48_);
v___f_51_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__3), 7, 6);
lean_closure_set(v___f_51_, 0, v_inst_44_);
lean_closure_set(v___f_51_, 1, v_inst_45_);
lean_closure_set(v___f_51_, 2, v_____do__lift_46_);
lean_closure_set(v___f_51_, 3, v_____do__lift_50_);
lean_closure_set(v___f_51_, 4, v_toPure_47_);
lean_closure_set(v___f_51_, 5, v_toBind_48_);
v___x_52_ = lean_apply_4(v_toBind_48_, lean_box(0), lean_box(0), v_inst_49_, v___f_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5(lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_toPure_56_, lean_object* v_toBind_57_, lean_object* v_inst_58_, lean_object* v_____do__lift_59_){
_start:
{
lean_object* v_getMCtx_60_; lean_object* v___f_61_; lean_object* v___x_62_; 
v_getMCtx_60_ = lean_ctor_get(v_inst_53_, 0);
lean_inc(v_getMCtx_60_);
lean_dec_ref(v_inst_53_);
lean_inc(v_toBind_57_);
v___f_61_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__4), 7, 6);
lean_closure_set(v___f_61_, 0, v_inst_54_);
lean_closure_set(v___f_61_, 1, v_inst_55_);
lean_closure_set(v___f_61_, 2, v_____do__lift_59_);
lean_closure_set(v___f_61_, 3, v_toPure_56_);
lean_closure_set(v___f_61_, 4, v_toBind_57_);
lean_closure_set(v___f_61_, 5, v_inst_58_);
v___x_62_ = lean_apply_4(v_toBind_57_, lean_box(0), lean_box(0), v_getMCtx_60_, v___f_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_){
_start:
{
lean_object* v_toApplicative_69_; lean_object* v_toBind_70_; lean_object* v_getEnv_71_; lean_object* v_toPure_72_; lean_object* v___f_73_; lean_object* v___x_74_; 
v_toApplicative_69_ = lean_ctor_get(v_inst_63_, 0);
lean_inc_ref(v_toApplicative_69_);
v_toBind_70_ = lean_ctor_get(v_inst_63_, 1);
lean_inc_n(v_toBind_70_, 2);
lean_dec_ref(v_inst_63_);
v_getEnv_71_ = lean_ctor_get(v_inst_64_, 0);
lean_inc(v_getEnv_71_);
lean_dec_ref(v_inst_64_);
v_toPure_72_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_inc(v_toPure_72_);
lean_dec_ref(v_toApplicative_69_);
v___f_73_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg___lam__5), 7, 6);
lean_closure_set(v___f_73_, 0, v_inst_65_);
lean_closure_set(v___f_73_, 1, v_inst_67_);
lean_closure_set(v___f_73_, 2, v_inst_68_);
lean_closure_set(v___f_73_, 3, v_toPure_72_);
lean_closure_set(v___f_73_, 4, v_toBind_70_);
lean_closure_set(v___f_73_, 5, v_inst_66_);
v___x_74_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v_getEnv_71_, v___f_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap(lean_object* v_m_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(v_inst_76_, v_inst_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_inst_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__0(lean_object* v_ctx_83_, lean_object* v_toPure_84_, lean_object* v_____do__lift_85_){
_start:
{
lean_object* v_env_86_; lean_object* v_cmdEnv_x3f_87_; lean_object* v_mctx_88_; lean_object* v_options_89_; lean_object* v_currNamespace_90_; lean_object* v_openDecls_91_; lean_object* v_ngen_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_env_86_ = lean_ctor_get(v_ctx_83_, 0);
v_cmdEnv_x3f_87_ = lean_ctor_get(v_ctx_83_, 1);
v_mctx_88_ = lean_ctor_get(v_ctx_83_, 3);
v_options_89_ = lean_ctor_get(v_ctx_83_, 4);
v_currNamespace_90_ = lean_ctor_get(v_ctx_83_, 5);
v_openDecls_91_ = lean_ctor_get(v_ctx_83_, 6);
v_ngen_92_ = lean_ctor_get(v_ctx_83_, 7);
v_isSharedCheck_100_ = !lean_is_exclusive(v_ctx_83_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v_ctx_83_, 2);
lean_dec(v_unused_101_);
v___x_94_ = v_ctx_83_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_ngen_92_);
lean_inc(v_openDecls_91_);
lean_inc(v_currNamespace_90_);
lean_inc(v_options_89_);
lean_inc(v_mctx_88_);
lean_inc(v_cmdEnv_x3f_87_);
lean_inc(v_env_86_);
lean_dec(v_ctx_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 2, v_____do__lift_85_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_env_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_cmdEnv_x3f_87_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_____do__lift_85_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_mctx_88_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_options_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 5, v_currNamespace_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 6, v_openDecls_91_);
lean_ctor_set(v_reuseFailAlloc_99_, 7, v_ngen_92_);
v___x_97_ = v_reuseFailAlloc_99_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_apply_2(v_toPure_84_, lean_box(0), v___x_97_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg___lam__1(lean_object* v_toPure_102_, lean_object* v_toBind_103_, lean_object* v_inst_104_, lean_object* v_ctx_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; 
v___f_106_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_save___redArg___lam__0), 3, 2);
lean_closure_set(v___f_106_, 0, v_ctx_105_);
lean_closure_set(v___f_106_, 1, v_toPure_102_);
v___x_107_ = lean_apply_4(v_toBind_103_, lean_box(0), lean_box(0), v_inst_104_, v___f_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___redArg(lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_){
_start:
{
lean_object* v_toApplicative_115_; lean_object* v_toBind_116_; lean_object* v_toPure_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
v_toApplicative_115_ = lean_ctor_get(v_inst_108_, 0);
v_toBind_116_ = lean_ctor_get(v_inst_108_, 1);
lean_inc_n(v_toBind_116_, 2);
v_toPure_117_ = lean_ctor_get(v_toApplicative_115_, 1);
lean_inc(v_toPure_117_);
v___x_118_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___redArg(v_inst_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Elab_CommandContextInfo_save___redArg___lam__1), 4, 3);
lean_closure_set(v___f_119_, 0, v_toPure_117_);
lean_closure_set(v___f_119_, 1, v_toBind_116_);
lean_closure_set(v___f_119_, 2, v_inst_114_);
v___x_120_ = lean_apply_4(v_toBind_116_, lean_box(0), lean_box(0), v___x_118_, v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save(lean_object* v_m_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_122_, v_inst_123_, v_inst_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_inst_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CustomInfo_format(lean_object* v_x_136_){
_start:
{
lean_object* v_value_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_151_; 
v_value_137_ = lean_ctor_get(v_x_136_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v_x_136_, 0);
lean_dec(v_unused_152_);
v___x_139_ = v_x_136_;
v_isShared_140_ = v_isSharedCheck_151_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_value_137_);
lean_dec(v_x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_151_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_CustomInfo_format___closed__1));
v___x_142_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_value_137_);
lean_dec(v_value_137_);
v___x_143_ = 1;
v___x_144_ = l_Lean_Name_toString(v___x_142_, v___x_143_);
v___x_145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 5);
lean_ctor_set(v___x_139_, 1, v___x_145_);
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_147_ = v___x_139_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_150_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_Elab_CustomInfo_format___closed__3));
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(lean_object* v_opts_155_, lean_object* v_opt_156_){
_start:
{
lean_object* v_name_157_; lean_object* v_defValue_158_; lean_object* v_map_159_; lean_object* v___x_160_; 
v_name_157_ = lean_ctor_get(v_opt_156_, 0);
v_defValue_158_ = lean_ctor_get(v_opt_156_, 1);
v_map_159_ = lean_ctor_get(v_opts_155_, 0);
v___x_160_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_159_, v_name_157_);
if (lean_obj_tag(v___x_160_) == 0)
{
uint8_t v___x_161_; 
v___x_161_ = lean_unbox(v_defValue_158_);
return v___x_161_;
}
else
{
lean_object* v_val_162_; 
v_val_162_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v___x_160_, 1);
if (lean_obj_tag(v_val_162_) == 1)
{
uint8_t v_v_163_; 
v_v_163_ = lean_ctor_get_uint8(v_val_162_, 0);
lean_dec_ref_known(v_val_162_, 0);
return v_v_163_;
}
else
{
uint8_t v___x_164_; 
lean_dec(v_val_162_);
v___x_164_ = lean_unbox(v_defValue_158_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0___boxed(lean_object* v_opts_165_, lean_object* v_opt_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_opts_165_, v_opt_166_);
lean_dec_ref(v_opt_166_);
lean_dec_ref(v_opts_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(lean_object* v_opts_169_, lean_object* v_opt_170_){
_start:
{
lean_object* v_name_171_; lean_object* v_defValue_172_; lean_object* v_map_173_; lean_object* v___x_174_; 
v_name_171_ = lean_ctor_get(v_opt_170_, 0);
v_defValue_172_ = lean_ctor_get(v_opt_170_, 1);
v_map_173_ = lean_ctor_get(v_opts_169_, 0);
v___x_174_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_173_, v_name_171_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_inc(v_defValue_172_);
return v_defValue_172_;
}
else
{
lean_object* v_val_175_; 
v_val_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_174_, 1);
if (lean_obj_tag(v_val_175_) == 3)
{
lean_object* v_v_176_; 
v_v_176_ = lean_ctor_get(v_val_175_, 0);
lean_inc(v_v_176_);
lean_dec_ref_known(v_val_175_, 1);
return v_v_176_;
}
else
{
lean_dec(v_val_175_);
lean_inc(v_defValue_172_);
return v_defValue_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1___boxed(lean_object* v_opts_177_, lean_object* v_opt_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_opts_177_, v_opt_178_);
lean_dec_ref(v_opt_178_);
lean_dec_ref(v_opts_177_);
return v_res_179_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_unsigned_to_nat(32u);
v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1(void){
_start:
{
size_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_183_ = ((size_t)5ULL);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_unsigned_to_nat(32u);
v___x_186_ = lean_mk_empty_array_with_capacity(v___x_185_);
v___x_187_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__0);
v___x_188_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_184_);
lean_ctor_set(v___x_188_, 3, v___x_184_);
lean_ctor_set_usize(v___x_188_, 4, v___x_183_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__2);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_NameSet_empty;
v___x_195_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
lean_ctor_set(v___x_196_, 2, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = l_Lean_firstFrontendMacroScope;
v___x_199_ = lean_nat_add(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8(void){
_start:
{
lean_object* v___x_204_; uint64_t v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_205_ = 0ULL;
v___x_206_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set_uint64(v___x_206_, sizeof(void*)*1, v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; 
v___x_207_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__1);
v___x_208_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__3);
v___x_209_ = 1;
v___x_210_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_207_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*3, v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = l_Lean_Options_empty;
v___x_218_ = l_Lean_Core_getMaxHeartbeats(v___x_217_);
return v___x_218_;
}
}
static uint8_t _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = l_Lean_diagnostics;
v___x_220_ = l_Lean_Options_empty;
v___x_221_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = l_Lean_maxRecDepth;
v___x_223_ = l_Lean_Options_empty;
v___x_224_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v___x_223_, v___x_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg(lean_object* v_info_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_a_229_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_toCommandContextInfo_236_; lean_object* v_env_237_; lean_object* v_options_238_; lean_object* v_currNamespace_239_; lean_object* v_openDecls_240_; lean_object* v_ngen_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v_env_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___y_255_; lean_object* v___y_256_; lean_object* v_fileName_257_; lean_object* v_fileMap_258_; lean_object* v_currRecDepth_259_; lean_object* v_ref_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v_initHeartbeats_263_; lean_object* v_maxHeartbeats_264_; lean_object* v_quotContext_265_; lean_object* v_currMacroScope_266_; lean_object* v_cancelTk_x3f_267_; uint8_t v_suppressElabErrors_268_; lean_object* v_inheritedTraceOptions_269_; lean_object* v___y_270_; uint8_t v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; uint8_t v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; uint8_t v___y_328_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_env_359_; lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___y_363_; lean_object* v___y_364_; uint8_t v___y_394_; uint8_t v___x_414_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__4);
v___x_234_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__5);
v___x_235_ = lean_io_get_num_heartbeats();
v_toCommandContextInfo_236_ = lean_ctor_get(v_info_225_, 0);
lean_inc_ref(v_toCommandContextInfo_236_);
lean_dec_ref(v_info_225_);
v_env_237_ = lean_ctor_get(v_toCommandContextInfo_236_, 0);
lean_inc_ref(v_env_237_);
v_options_238_ = lean_ctor_get(v_toCommandContextInfo_236_, 4);
lean_inc_ref(v_options_238_);
v_currNamespace_239_ = lean_ctor_get(v_toCommandContextInfo_236_, 5);
lean_inc(v_currNamespace_239_);
v_openDecls_240_ = lean_ctor_get(v_toCommandContextInfo_236_, 6);
lean_inc(v_openDecls_240_);
v_ngen_241_ = lean_ctor_get(v_toCommandContextInfo_236_, 7);
lean_inc_ref(v_ngen_241_);
lean_dec_ref(v_toCommandContextInfo_236_);
v___x_242_ = l_Lean_firstFrontendMacroScope;
v___x_243_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__6);
v___x_244_ = 0;
v_env_245_ = l_Lean_Environment_setExporting(v_env_237_, v___x_244_);
v___x_246_ = lean_box(0);
v___x_247_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__7));
v___x_248_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__8);
v___x_249_ = 1;
v___x_250_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__9);
v___x_251_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__10));
v___x_252_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_252_, 0, v_env_245_);
lean_ctor_set(v___x_252_, 1, v___x_243_);
lean_ctor_set(v___x_252_, 2, v_ngen_241_);
lean_ctor_set(v___x_252_, 3, v___x_247_);
lean_ctor_set(v___x_252_, 4, v___x_248_);
lean_ctor_set(v___x_252_, 5, v___x_233_);
lean_ctor_set(v___x_252_, 6, v___x_234_);
lean_ctor_set(v___x_252_, 7, v___x_250_);
lean_ctor_set(v___x_252_, 8, v___x_251_);
v___x_253_ = lean_st_mk_ref(v___x_252_);
v___x_348_ = l_Lean_inheritedTraceOptions;
v___x_349_ = lean_st_ref_get(v___x_348_);
v___x_350_ = lean_st_ref_get(v___x_253_);
v___x_351_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__14));
v___x_352_ = l_Lean_instInhabitedFileMap_default;
v___x_353_ = l_Lean_Options_empty;
v___x_354_ = lean_unsigned_to_nat(1000u);
v___x_355_ = lean_box(0);
v___x_356_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__15);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_358_, 0, v___x_351_);
lean_ctor_set(v___x_358_, 1, v___x_352_);
lean_ctor_set(v___x_358_, 2, v___x_353_);
lean_ctor_set(v___x_358_, 3, v___x_232_);
lean_ctor_set(v___x_358_, 4, v___x_354_);
lean_ctor_set(v___x_358_, 5, v___x_355_);
lean_ctor_set(v___x_358_, 6, v_currNamespace_239_);
lean_ctor_set(v___x_358_, 7, v_openDecls_240_);
lean_ctor_set(v___x_358_, 8, v___x_235_);
lean_ctor_set(v___x_358_, 9, v___x_356_);
lean_ctor_set(v___x_358_, 10, v___x_246_);
lean_ctor_set(v___x_358_, 11, v___x_242_);
lean_ctor_set(v___x_358_, 12, v___x_357_);
lean_ctor_set(v___x_358_, 13, v___x_349_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*14, v___x_244_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*14 + 1, v___x_244_);
v_env_359_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_env_359_);
lean_dec(v___x_350_);
v___x_360_ = l_Lean_diagnostics;
v___x_361_ = lean_uint8_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__16);
v___x_414_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_359_);
lean_dec_ref(v_env_359_);
if (v___x_414_ == 0)
{
if (v___x_361_ == 0)
{
lean_inc(v___x_253_);
v___y_363_ = v___x_358_;
v___y_364_ = v___x_253_;
goto v___jp_362_;
}
else
{
v___y_394_ = v___x_414_;
goto v___jp_393_;
}
}
else
{
v___y_394_ = v___x_361_;
goto v___jp_393_;
}
v___jp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_mk_io_user_error(v_a_229_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
v___jp_254_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__1(v_options_238_, v___y_256_);
v___x_272_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_272_, 0, v_fileName_257_);
lean_ctor_set(v___x_272_, 1, v_fileMap_258_);
lean_ctor_set(v___x_272_, 2, v_options_238_);
lean_ctor_set(v___x_272_, 3, v_currRecDepth_259_);
lean_ctor_set(v___x_272_, 4, v___x_271_);
lean_ctor_set(v___x_272_, 5, v_ref_260_);
lean_ctor_set(v___x_272_, 6, v_currNamespace_261_);
lean_ctor_set(v___x_272_, 7, v_openDecls_262_);
lean_ctor_set(v___x_272_, 8, v_initHeartbeats_263_);
lean_ctor_set(v___x_272_, 9, v_maxHeartbeats_264_);
lean_ctor_set(v___x_272_, 10, v_quotContext_265_);
lean_ctor_set(v___x_272_, 11, v_currMacroScope_266_);
lean_ctor_set(v___x_272_, 12, v_cancelTk_x3f_267_);
lean_ctor_set(v___x_272_, 13, v_inheritedTraceOptions_269_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*14, v___y_255_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*14 + 1, v_suppressElabErrors_268_);
v___x_273_ = lean_apply_3(v_x_226_, v___x_272_, v___y_270_, lean_box(0));
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_st_ref_get(v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_278_);
if (v_isShared_277_ == 0)
{
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_274_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_304_; 
lean_dec(v___x_253_);
v_a_283_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_304_ == 0)
{
v___x_285_ = v___x_273_;
v_isShared_286_ = v_isSharedCheck_304_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_304_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
if (lean_obj_tag(v_a_283_) == 0)
{
lean_object* v_msg_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v_msg_287_ = lean_ctor_get(v_a_283_, 1);
lean_inc_ref(v_msg_287_);
lean_dec_ref_known(v_a_283_, 2);
v___x_288_ = l_Lean_MessageData_toString(v_msg_287_);
v___x_289_ = lean_mk_io_user_error(v___x_288_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_289_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
else
{
lean_object* v_id_293_; lean_object* v___x_294_; 
lean_del_object(v___x_285_);
v_id_293_ = lean_ctor_get(v_a_283_, 0);
lean_inc(v_id_293_);
lean_dec_ref_known(v_a_283_, 2);
v___x_294_ = l_Lean_InternalExceptionId_getName(v_id_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_id_293_);
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___x_296_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__11));
v___x_297_ = l_Lean_Name_toString(v_a_295_, v___x_249_);
v___x_298_ = lean_string_append(v___x_296_, v___x_297_);
lean_dec_ref(v___x_297_);
v_a_229_ = v___x_298_;
goto v___jp_228_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref_known(v___x_294_, 1);
v___x_299_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__12));
v___x_300_ = l_Nat_reprFast(v_id_293_);
v___x_301_ = lean_string_append(v___x_299_, v___x_300_);
lean_dec_ref(v___x_300_);
v___x_302_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__13));
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
v_a_229_ = v___x_303_;
goto v___jp_228_;
}
}
}
}
}
v___jp_305_:
{
lean_object* v_fileName_310_; lean_object* v_fileMap_311_; lean_object* v_currRecDepth_312_; lean_object* v_ref_313_; lean_object* v_currNamespace_314_; lean_object* v_openDecls_315_; lean_object* v_initHeartbeats_316_; lean_object* v_maxHeartbeats_317_; lean_object* v_quotContext_318_; lean_object* v_currMacroScope_319_; lean_object* v_cancelTk_x3f_320_; uint8_t v_suppressElabErrors_321_; lean_object* v_inheritedTraceOptions_322_; 
v_fileName_310_ = lean_ctor_get(v___y_308_, 0);
lean_inc_ref(v_fileName_310_);
v_fileMap_311_ = lean_ctor_get(v___y_308_, 1);
lean_inc_ref(v_fileMap_311_);
v_currRecDepth_312_ = lean_ctor_get(v___y_308_, 3);
lean_inc(v_currRecDepth_312_);
v_ref_313_ = lean_ctor_get(v___y_308_, 5);
lean_inc(v_ref_313_);
v_currNamespace_314_ = lean_ctor_get(v___y_308_, 6);
lean_inc(v_currNamespace_314_);
v_openDecls_315_ = lean_ctor_get(v___y_308_, 7);
lean_inc(v_openDecls_315_);
v_initHeartbeats_316_ = lean_ctor_get(v___y_308_, 8);
lean_inc(v_initHeartbeats_316_);
v_maxHeartbeats_317_ = lean_ctor_get(v___y_308_, 9);
lean_inc(v_maxHeartbeats_317_);
v_quotContext_318_ = lean_ctor_get(v___y_308_, 10);
lean_inc(v_quotContext_318_);
v_currMacroScope_319_ = lean_ctor_get(v___y_308_, 11);
lean_inc(v_currMacroScope_319_);
v_cancelTk_x3f_320_ = lean_ctor_get(v___y_308_, 12);
lean_inc(v_cancelTk_x3f_320_);
v_suppressElabErrors_321_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_322_ = lean_ctor_get(v___y_308_, 13);
lean_inc_ref(v_inheritedTraceOptions_322_);
lean_dec_ref(v___y_308_);
v___y_255_ = v___y_306_;
v___y_256_ = v___y_307_;
v_fileName_257_ = v_fileName_310_;
v_fileMap_258_ = v_fileMap_311_;
v_currRecDepth_259_ = v_currRecDepth_312_;
v_ref_260_ = v_ref_313_;
v_currNamespace_261_ = v_currNamespace_314_;
v_openDecls_262_ = v_openDecls_315_;
v_initHeartbeats_263_ = v_initHeartbeats_316_;
v_maxHeartbeats_264_ = v_maxHeartbeats_317_;
v_quotContext_265_ = v_quotContext_318_;
v_currMacroScope_266_ = v_currMacroScope_319_;
v_cancelTk_x3f_267_ = v_cancelTk_x3f_320_;
v_suppressElabErrors_268_ = v_suppressElabErrors_321_;
v_inheritedTraceOptions_269_ = v_inheritedTraceOptions_322_;
v___y_270_ = v___y_309_;
goto v___jp_254_;
}
v___jp_323_:
{
if (v___y_328_ == 0)
{
lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v_nextMacroScope_331_; lean_object* v_ngen_332_; lean_object* v_auxDeclNGen_333_; lean_object* v_traceState_334_; lean_object* v_messages_335_; lean_object* v_infoState_336_; lean_object* v_snapshotTasks_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_346_; 
v___x_329_ = lean_st_ref_take(v___y_325_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
v_nextMacroScope_331_ = lean_ctor_get(v___x_329_, 1);
v_ngen_332_ = lean_ctor_get(v___x_329_, 2);
v_auxDeclNGen_333_ = lean_ctor_get(v___x_329_, 3);
v_traceState_334_ = lean_ctor_get(v___x_329_, 4);
v_messages_335_ = lean_ctor_get(v___x_329_, 6);
v_infoState_336_ = lean_ctor_get(v___x_329_, 7);
v_snapshotTasks_337_ = lean_ctor_get(v___x_329_, 8);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; 
v_unused_347_ = lean_ctor_get(v___x_329_, 5);
lean_dec(v_unused_347_);
v___x_339_ = v___x_329_;
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snapshotTasks_337_);
lean_inc(v_infoState_336_);
lean_inc(v_messages_335_);
lean_inc(v_traceState_334_);
lean_inc(v_auxDeclNGen_333_);
lean_inc(v_ngen_332_);
lean_inc(v_nextMacroScope_331_);
lean_inc(v_env_330_);
lean_dec(v___x_329_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = l_Lean_Kernel_enableDiag(v_env_330_, v___y_324_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 5, v___x_233_);
lean_ctor_set(v___x_339_, 0, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_nextMacroScope_331_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_ngen_332_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v_auxDeclNGen_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v_traceState_334_);
lean_ctor_set(v_reuseFailAlloc_345_, 5, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_345_, 6, v_messages_335_);
lean_ctor_set(v_reuseFailAlloc_345_, 7, v_infoState_336_);
lean_ctor_set(v_reuseFailAlloc_345_, 8, v_snapshotTasks_337_);
v___x_343_ = v_reuseFailAlloc_345_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; 
v___x_344_ = lean_st_ref_put(v___y_325_, v___x_343_);
v___y_306_ = v___y_324_;
v___y_307_ = v___y_326_;
v___y_308_ = v___y_327_;
v___y_309_ = v___y_325_;
goto v___jp_305_;
}
}
}
else
{
v___y_306_ = v___y_324_;
v___y_307_ = v___y_326_;
v___y_308_ = v___y_327_;
v___y_309_ = v___y_325_;
goto v___jp_305_;
}
}
v___jp_362_:
{
lean_object* v___x_365_; lean_object* v_fileName_366_; lean_object* v_fileMap_367_; lean_object* v_currRecDepth_368_; lean_object* v_ref_369_; lean_object* v_currNamespace_370_; lean_object* v_openDecls_371_; lean_object* v_initHeartbeats_372_; lean_object* v_maxHeartbeats_373_; lean_object* v_quotContext_374_; lean_object* v_currMacroScope_375_; lean_object* v_cancelTk_x3f_376_; uint8_t v_suppressElabErrors_377_; lean_object* v_inheritedTraceOptions_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_390_; 
v___x_365_ = lean_st_ref_get(v___y_364_);
v_fileName_366_ = lean_ctor_get(v___y_363_, 0);
v_fileMap_367_ = lean_ctor_get(v___y_363_, 1);
v_currRecDepth_368_ = lean_ctor_get(v___y_363_, 3);
v_ref_369_ = lean_ctor_get(v___y_363_, 5);
v_currNamespace_370_ = lean_ctor_get(v___y_363_, 6);
v_openDecls_371_ = lean_ctor_get(v___y_363_, 7);
v_initHeartbeats_372_ = lean_ctor_get(v___y_363_, 8);
v_maxHeartbeats_373_ = lean_ctor_get(v___y_363_, 9);
v_quotContext_374_ = lean_ctor_get(v___y_363_, 10);
v_currMacroScope_375_ = lean_ctor_get(v___y_363_, 11);
v_cancelTk_x3f_376_ = lean_ctor_get(v___y_363_, 12);
v_suppressElabErrors_377_ = lean_ctor_get_uint8(v___y_363_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_378_ = lean_ctor_get(v___y_363_, 13);
v_isSharedCheck_390_ = !lean_is_exclusive(v___y_363_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; lean_object* v_unused_392_; 
v_unused_391_ = lean_ctor_get(v___y_363_, 4);
lean_dec(v_unused_391_);
v_unused_392_ = lean_ctor_get(v___y_363_, 2);
lean_dec(v_unused_392_);
v___x_380_ = v___y_363_;
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_inheritedTraceOptions_378_);
lean_inc(v_cancelTk_x3f_376_);
lean_inc(v_currMacroScope_375_);
lean_inc(v_quotContext_374_);
lean_inc(v_maxHeartbeats_373_);
lean_inc(v_initHeartbeats_372_);
lean_inc(v_openDecls_371_);
lean_inc(v_currNamespace_370_);
lean_inc(v_ref_369_);
lean_inc(v_currRecDepth_368_);
lean_inc(v_fileMap_367_);
lean_inc(v_fileName_366_);
lean_dec(v___y_363_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_env_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v_env_382_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_382_);
lean_dec(v___x_365_);
v___x_383_ = l_Lean_maxRecDepth;
v___x_384_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17, &l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17_once, _init_l_Lean_Elab_ContextInfo_runCoreM___redArg___closed__17);
lean_inc_ref(v_inheritedTraceOptions_378_);
lean_inc(v_cancelTk_x3f_376_);
lean_inc(v_currMacroScope_375_);
lean_inc(v_quotContext_374_);
lean_inc(v_maxHeartbeats_373_);
lean_inc(v_initHeartbeats_372_);
lean_inc(v_openDecls_371_);
lean_inc(v_currNamespace_370_);
lean_inc(v_ref_369_);
lean_inc(v_currRecDepth_368_);
lean_inc_ref(v_fileMap_367_);
lean_inc_ref(v_fileName_366_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 4, v___x_384_);
lean_ctor_set(v___x_380_, 2, v___x_353_);
v___x_386_ = v___x_380_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_fileName_366_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_fileMap_367_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_currRecDepth_368_);
lean_ctor_set(v_reuseFailAlloc_389_, 4, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_389_, 5, v_ref_369_);
lean_ctor_set(v_reuseFailAlloc_389_, 6, v_currNamespace_370_);
lean_ctor_set(v_reuseFailAlloc_389_, 7, v_openDecls_371_);
lean_ctor_set(v_reuseFailAlloc_389_, 8, v_initHeartbeats_372_);
lean_ctor_set(v_reuseFailAlloc_389_, 9, v_maxHeartbeats_373_);
lean_ctor_set(v_reuseFailAlloc_389_, 10, v_quotContext_374_);
lean_ctor_set(v_reuseFailAlloc_389_, 11, v_currMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_389_, 12, v_cancelTk_x3f_376_);
lean_ctor_set(v_reuseFailAlloc_389_, 13, v_inheritedTraceOptions_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_389_, sizeof(void*)*14 + 1, v_suppressElabErrors_377_);
v___x_386_ = v_reuseFailAlloc_389_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
uint8_t v___x_387_; uint8_t v___x_388_; 
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*14, v___x_361_);
v___x_387_ = l_Lean_Option_get___at___00Lean_Elab_ContextInfo_runCoreM_spec__0(v_options_238_, v___x_360_);
v___x_388_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_382_);
lean_dec_ref(v_env_382_);
if (v___x_388_ == 0)
{
if (v___x_387_ == 0)
{
lean_dec_ref(v___x_386_);
v___y_255_ = v___x_387_;
v___y_256_ = v___x_383_;
v_fileName_257_ = v_fileName_366_;
v_fileMap_258_ = v_fileMap_367_;
v_currRecDepth_259_ = v_currRecDepth_368_;
v_ref_260_ = v_ref_369_;
v_currNamespace_261_ = v_currNamespace_370_;
v_openDecls_262_ = v_openDecls_371_;
v_initHeartbeats_263_ = v_initHeartbeats_372_;
v_maxHeartbeats_264_ = v_maxHeartbeats_373_;
v_quotContext_265_ = v_quotContext_374_;
v_currMacroScope_266_ = v_currMacroScope_375_;
v_cancelTk_x3f_267_ = v_cancelTk_x3f_376_;
v_suppressElabErrors_268_ = v_suppressElabErrors_377_;
v_inheritedTraceOptions_269_ = v_inheritedTraceOptions_378_;
v___y_270_ = v___y_364_;
goto v___jp_254_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_378_);
lean_dec(v_cancelTk_x3f_376_);
lean_dec(v_currMacroScope_375_);
lean_dec(v_quotContext_374_);
lean_dec(v_maxHeartbeats_373_);
lean_dec(v_initHeartbeats_372_);
lean_dec(v_openDecls_371_);
lean_dec(v_currNamespace_370_);
lean_dec(v_ref_369_);
lean_dec(v_currRecDepth_368_);
lean_dec_ref(v_fileMap_367_);
lean_dec_ref(v_fileName_366_);
v___y_324_ = v___x_387_;
v___y_325_ = v___y_364_;
v___y_326_ = v___x_383_;
v___y_327_ = v___x_386_;
v___y_328_ = v___x_388_;
goto v___jp_323_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_378_);
lean_dec(v_cancelTk_x3f_376_);
lean_dec(v_currMacroScope_375_);
lean_dec(v_quotContext_374_);
lean_dec(v_maxHeartbeats_373_);
lean_dec(v_initHeartbeats_372_);
lean_dec(v_openDecls_371_);
lean_dec(v_currNamespace_370_);
lean_dec(v_ref_369_);
lean_dec(v_currRecDepth_368_);
lean_dec_ref(v_fileMap_367_);
lean_dec_ref(v_fileName_366_);
v___y_324_ = v___x_387_;
v___y_325_ = v___y_364_;
v___y_326_ = v___x_383_;
v___y_327_ = v___x_386_;
v___y_328_ = v___x_387_;
goto v___jp_323_;
}
}
}
}
v___jp_393_:
{
if (v___y_394_ == 0)
{
lean_object* v___x_395_; lean_object* v_env_396_; lean_object* v_nextMacroScope_397_; lean_object* v_ngen_398_; lean_object* v_auxDeclNGen_399_; lean_object* v_traceState_400_; lean_object* v_messages_401_; lean_object* v_infoState_402_; lean_object* v_snapshotTasks_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_412_; 
v___x_395_ = lean_st_ref_take(v___x_253_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
v_nextMacroScope_397_ = lean_ctor_get(v___x_395_, 1);
v_ngen_398_ = lean_ctor_get(v___x_395_, 2);
v_auxDeclNGen_399_ = lean_ctor_get(v___x_395_, 3);
v_traceState_400_ = lean_ctor_get(v___x_395_, 4);
v_messages_401_ = lean_ctor_get(v___x_395_, 6);
v_infoState_402_ = lean_ctor_get(v___x_395_, 7);
v_snapshotTasks_403_ = lean_ctor_get(v___x_395_, 8);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_395_, 5);
lean_dec(v_unused_413_);
v___x_405_ = v___x_395_;
v_isShared_406_ = v_isSharedCheck_412_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snapshotTasks_403_);
lean_inc(v_infoState_402_);
lean_inc(v_messages_401_);
lean_inc(v_traceState_400_);
lean_inc(v_auxDeclNGen_399_);
lean_inc(v_ngen_398_);
lean_inc(v_nextMacroScope_397_);
lean_inc(v_env_396_);
lean_dec(v___x_395_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_412_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = l_Lean_Kernel_enableDiag(v_env_396_, v___x_361_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 5, v___x_233_);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_397_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_398_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_399_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_traceState_400_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_messages_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_infoState_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_snapshotTasks_403_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = lean_st_ref_put(v___x_253_, v___x_409_);
lean_inc(v___x_253_);
v___y_363_ = v___x_358_;
v___y_364_ = v___x_253_;
goto v___jp_362_;
}
}
}
else
{
lean_inc(v___x_253_);
v___y_363_ = v___x_358_;
v___y_364_ = v___x_253_;
goto v___jp_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___redArg___boxed(lean_object* v_info_415_, lean_object* v_x_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_415_, v_x_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM(lean_object* v_00_u03b1_419_, lean_object* v_info_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_420_, v_x_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runCoreM___boxed(lean_object* v_00_u03b1_424_, lean_object* v_info_425_, lean_object* v_x_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Elab_ContextInfo_runCoreM(v_00_u03b1_424_, v_info_425_, v_x_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(lean_object* v___x_429_, lean_object* v_x_430_, lean_object* v___x_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_st_mk_ref(v___x_429_);
lean_inc(v___x_435_);
v___x_436_ = lean_apply_5(v_x_430_, v___x_431_, v___x_435_, v___y_432_, v___y_433_, lean_box(0));
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_446_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_446_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = lean_st_ref_get(v___x_435_);
lean_dec(v___x_435_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_a_437_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v___x_435_);
v_a_447_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_436_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_436_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed(lean_object* v___x_455_, lean_object* v_x_456_, lean_object* v___x_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0(v___x_455_, v_x_456_, v___x_457_, v___y_458_, v___y_459_);
return v_res_461_;
}
}
static uint64_t _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1(void){
_start:
{
lean_object* v___x_468_; uint64_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_469_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2(void){
_start:
{
uint64_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_uint64_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__1);
v___x_471_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__0));
v___x_472_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set_uint64(v___x_472_, sizeof(void*)*1, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__4);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_479_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
lean_ctor_set(v___x_479_, 3, v___x_478_);
lean_ctor_set(v___x_479_, 4, v___x_478_);
lean_ctor_set(v___x_479_, 5, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_unsigned_to_nat(32u);
v___x_481_ = lean_mk_empty_array_with_capacity(v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8(void){
_start:
{
size_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_483_ = ((size_t)5ULL);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_unsigned_to_nat(32u);
v___x_486_ = lean_mk_empty_array_with_capacity(v___x_485_);
v___x_487_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__7);
v___x_488_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
lean_ctor_set(v___x_488_, 2, v___x_484_);
lean_ctor_set(v___x_488_, 3, v___x_484_);
lean_ctor_set_usize(v___x_488_, 4, v___x_483_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__5);
v___x_490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
lean_ctor_set(v___x_490_, 2, v___x_489_);
lean_ctor_set(v___x_490_, 3, v___x_489_);
lean_ctor_set(v___x_490_, 4, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object* v_info_491_, lean_object* v_lctx_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_toCommandContextInfo_503_; lean_object* v_mctx_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___f_509_; lean_object* v___x_510_; 
v___x_495_ = lean_box(1);
v___x_496_ = 0;
v___x_497_ = 1;
v___x_498_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__2);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = ((lean_object*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__3));
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_502_, 0, v___x_498_);
lean_ctor_set(v___x_502_, 1, v___x_495_);
lean_ctor_set(v___x_502_, 2, v_lctx_492_);
lean_ctor_set(v___x_502_, 3, v___x_500_);
lean_ctor_set(v___x_502_, 4, v___x_501_);
lean_ctor_set(v___x_502_, 5, v___x_499_);
lean_ctor_set(v___x_502_, 6, v___x_501_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7, v___x_496_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 1, v___x_496_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 2, v___x_496_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*7 + 3, v___x_497_);
v_toCommandContextInfo_503_ = lean_ctor_get(v_info_491_, 0);
v_mctx_504_ = lean_ctor_get(v_toCommandContextInfo_503_, 3);
v___x_505_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__6);
v___x_506_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__8);
v___x_507_ = lean_obj_once(&l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9, &l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9_once, _init_l_Lean_Elab_ContextInfo_runMetaM___redArg___closed__9);
lean_inc_ref(v_mctx_504_);
v___x_508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_508_, 0, v_mctx_504_);
lean_ctor_set(v___x_508_, 1, v___x_505_);
lean_ctor_set(v___x_508_, 2, v___x_495_);
lean_ctor_set(v___x_508_, 3, v___x_506_);
lean_ctor_set(v___x_508_, 4, v___x_507_);
v___f_509_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_509_, 0, v___x_508_);
lean_closure_set(v___f_509_, 1, v_x_493_);
lean_closure_set(v___f_509_, 2, v___x_502_);
v___x_510_ = l_Lean_Elab_ContextInfo_runCoreM___redArg(v_info_491_, v___f_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_519_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_519_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_fst_515_; lean_object* v___x_517_; 
v_fst_515_ = lean_ctor_get(v_a_511_, 0);
lean_inc(v_fst_515_);
lean_dec(v_a_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v_fst_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_fst_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_510_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_510_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg___boxed(lean_object* v_info_528_, lean_object* v_lctx_529_, lean_object* v_x_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_528_, v_lctx_529_, v_x_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* v_00_u03b1_533_, lean_object* v_info_534_, lean_object* v_lctx_535_, lean_object* v_x_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_info_534_, v_lctx_535_, v_x_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_runMetaM___boxed(lean_object* v_00_u03b1_539_, lean_object* v_info_540_, lean_object* v_lctx_541_, lean_object* v_x_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_ContextInfo_runMetaM(v_00_u03b1_539_, v_info_540_, v_lctx_541_, v_x_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* v_info_545_, lean_object* v_lctx_546_){
_start:
{
lean_object* v_toCommandContextInfo_547_; lean_object* v_env_548_; lean_object* v_mctx_549_; lean_object* v_options_550_; lean_object* v_currNamespace_551_; lean_object* v_openDecls_552_; lean_object* v___x_553_; 
v_toCommandContextInfo_547_ = lean_ctor_get(v_info_545_, 0);
v_env_548_ = lean_ctor_get(v_toCommandContextInfo_547_, 0);
v_mctx_549_ = lean_ctor_get(v_toCommandContextInfo_547_, 3);
v_options_550_ = lean_ctor_get(v_toCommandContextInfo_547_, 4);
v_currNamespace_551_ = lean_ctor_get(v_toCommandContextInfo_547_, 5);
v_openDecls_552_ = lean_ctor_get(v_toCommandContextInfo_547_, 6);
lean_inc(v_openDecls_552_);
lean_inc(v_currNamespace_551_);
lean_inc_ref(v_options_550_);
lean_inc_ref(v_mctx_549_);
lean_inc_ref(v_env_548_);
v___x_553_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_553_, 0, v_env_548_);
lean_ctor_set(v___x_553_, 1, v_mctx_549_);
lean_ctor_set(v___x_553_, 2, v_lctx_546_);
lean_ctor_set(v___x_553_, 3, v_options_550_);
lean_ctor_set(v___x_553_, 4, v_currNamespace_551_);
lean_ctor_set(v___x_553_, 5, v_openDecls_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* v_info_554_, lean_object* v_lctx_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_554_, v_lctx_555_);
lean_dec_ref(v_info_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* v_info_557_, lean_object* v_lctx_558_, lean_object* v_stx_559_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = l_Lean_Elab_ContextInfo_toPPContext(v_info_557_, v_lctx_558_);
v___x_562_ = l_Lean_ppTerm(v___x_561_, v_stx_559_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* v_info_564_, lean_object* v_lctx_565_, lean_object* v_stx_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Elab_ContextInfo_ppSyntax(v_info_564_, v_lctx_565_, v_stx_566_);
lean_dec_ref(v_info_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(lean_object* v_ctx_584_, lean_object* v_pos_585_, lean_object* v_info_586_){
_start:
{
lean_object* v_toCommandContextInfo_587_; lean_object* v_fileMap_588_; lean_object* v___x_589_; lean_object* v_line_590_; lean_object* v_column_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_toCommandContextInfo_587_ = lean_ctor_get(v_ctx_584_, 0);
lean_inc_ref(v_toCommandContextInfo_587_);
lean_dec_ref(v_ctx_584_);
v_fileMap_588_ = lean_ctor_get(v_toCommandContextInfo_587_, 2);
lean_inc_ref(v_fileMap_588_);
lean_dec_ref(v_toCommandContextInfo_587_);
v___x_589_ = l_Lean_FileMap_toPosition(v_fileMap_588_, v_pos_585_);
v_line_590_ = lean_ctor_get(v___x_589_, 0);
v_column_591_ = lean_ctor_get(v___x_589_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_column_591_);
lean_inc(v_line_590_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_596_ = l_Nat_reprFast(v_line_590_);
v___x_597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 5);
lean_ctor_set(v___x_593_, 1, v___x_597_);
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_599_ = v___x_593_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_597_);
v___x_599_ = v_reuseFailAlloc_613_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_pos_606_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Nat_reprFast(v_column_591_);
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_601_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v_pos_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_pos_606_, 0, v___x_604_);
lean_ctor_set(v_pos_606_, 1, v___x_605_);
switch(lean_obj_tag(v_info_586_))
{
case 0:
{
return v_pos_606_;
}
case 1:
{
uint8_t v_canonical_610_; 
v_canonical_610_ = lean_ctor_get_uint8(v_info_586_, sizeof(void*)*2);
if (v_canonical_610_ == 1)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__9));
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v_pos_606_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
return v___x_612_;
}
else
{
goto v___jp_607_;
}
}
default: 
{
goto v___jp_607_;
}
}
v___jp_607_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__7));
v___x_609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_609_, 0, v_pos_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___boxed(lean_object* v_ctx_615_, lean_object* v_pos_616_, lean_object* v_info_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_615_, v_pos_616_, v_info_617_);
lean_dec(v_info_617_);
lean_dec(v_pos_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(lean_object* v_ctx_622_, lean_object* v_stx_623_){
_start:
{
lean_object* v___y_625_; lean_object* v___y_626_; uint8_t v___x_634_; lean_object* v___y_636_; lean_object* v___x_639_; 
v___x_634_ = 0;
v___x_639_ = l_Lean_Syntax_getPos_x3f(v_stx_623_, v___x_634_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___y_636_ = v___x_640_;
goto v___jp_635_;
}
else
{
lean_object* v_val_641_; 
v_val_641_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v___x_639_, 1);
v___y_636_ = v_val_641_;
goto v___jp_635_;
}
v___jp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_627_ = l_Lean_Syntax_getHeadInfo(v_stx_623_);
lean_inc_ref(v_ctx_622_);
v___x_628_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_622_, v___y_625_, v___x_627_);
lean_dec(v___x_627_);
lean_dec(v___y_625_);
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_Syntax_getTailInfo(v_stx_623_);
v___x_632_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos(v_ctx_622_, v___y_626_, v___x_631_);
lean_dec(v___x_631_);
lean_dec(v___y_626_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_630_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
v___jp_635_:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Syntax_getTailPos_x3f(v_stx_623_, v___x_634_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_inc(v___y_636_);
v___y_625_ = v___y_636_;
v___y_626_ = v___y_636_;
goto v___jp_624_;
}
else
{
lean_object* v_val_638_; 
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v___x_637_, 1);
v___y_625_ = v___y_636_;
v___y_626_ = v_val_638_;
goto v___jp_624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___boxed(lean_object* v_ctx_642_, lean_object* v_stx_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_642_, v_stx_643_);
lean_dec(v_stx_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(lean_object* v_ctx_648_, lean_object* v_info_649_){
_start:
{
lean_object* v_elaborator_650_; lean_object* v_stx_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_666_; 
v_elaborator_650_ = lean_ctor_get(v_info_649_, 0);
v_stx_651_ = lean_ctor_get(v_info_649_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_info_649_);
if (v_isSharedCheck_666_ == 0)
{
v___x_653_ = v_info_649_;
v_isShared_654_ = v_isSharedCheck_666_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_stx_651_);
lean_inc(v_elaborator_650_);
lean_dec(v_info_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_666_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint8_t v___x_655_; 
v___x_655_ = l_Lean_Name_isAnonymous(v_elaborator_650_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_648_, v_stx_651_);
lean_dec(v_stx_651_);
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 5);
lean_ctor_set(v___x_653_, 1, v___x_657_);
lean_ctor_set(v___x_653_, 0, v___x_656_);
v___x_659_ = v___x_653_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_664_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_660_ = 1;
v___x_661_ = l_Lean_Name_toString(v_elaborator_650_, v___x_660_);
v___x_662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_659_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
return v___x_663_;
}
}
else
{
lean_object* v___x_665_; 
lean_del_object(v___x_653_);
lean_dec(v_elaborator_650_);
v___x_665_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_648_, v_stx_651_);
lean_dec(v_stx_651_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object* v_info_667_, lean_object* v_ctx_668_, lean_object* v_x_669_){
_start:
{
lean_object* v_lctx_671_; lean_object* v___x_672_; 
v_lctx_671_ = lean_ctor_get(v_info_667_, 1);
lean_inc_ref(v_lctx_671_);
lean_dec_ref(v_info_667_);
v___x_672_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_668_, v_lctx_671_, v_x_669_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg___boxed(lean_object* v_info_673_, lean_object* v_ctx_674_, lean_object* v_x_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_673_, v_ctx_674_, v_x_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM(lean_object* v_00_u03b1_678_, lean_object* v_info_679_, lean_object* v_ctx_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_679_, v_ctx_680_, v_x_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_runMetaM___boxed(lean_object* v_00_u03b1_684_, lean_object* v_info_685_, lean_object* v_ctx_686_, lean_object* v_x_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Elab_TermInfo_runMetaM(v_00_u03b1_684_, v_info_685_, v_ctx_686_, v_x_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0(lean_object* v_ctx_704_, lean_object* v_toElabInfo_705_, lean_object* v_expr_706_, uint8_t v_isBinder_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v_a_728_; lean_object* v___y_738_; uint8_t v___y_739_; lean_object* v___y_742_; lean_object* v_a_743_; lean_object* v___x_746_; 
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc_ref(v_expr_706_);
v___x_746_ = lean_infer_type(v_expr_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l_Lean_Meta_ppExpr(v_a_747_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v_a_728_ = v_a_749_;
goto v___jp_727_;
}
else
{
lean_object* v_a_750_; 
v_a_750_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_750_);
v___y_742_ = v___x_748_;
v_a_743_ = v_a_750_;
goto v___jp_741_;
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_746_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_746_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
lean_inc(v_a_751_);
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v___y_742_ = v___x_756_;
v_a_743_ = v_a_751_;
goto v___jp_741_;
}
}
}
v___jp_713_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc_ref(v___y_716_);
v___x_717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_717_, 0, v___y_716_);
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___y_715_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___y_714_);
v___x_722_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_704_, v_toElabInfo_705_);
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
v___jp_727_:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_ppExpr(v_expr_706_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__3));
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_a_730_);
v___x_733_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
v___x_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
if (v_isBinder_707_ == 0)
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__6));
v___y_714_ = v_a_728_;
v___y_715_ = v___x_734_;
v___y_716_ = v___x_735_;
goto v___jp_713_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__7));
v___y_714_ = v_a_728_;
v___y_715_ = v___x_734_;
v___y_716_ = v___x_736_;
goto v___jp_713_;
}
}
else
{
lean_dec(v_a_728_);
lean_dec_ref(v_toElabInfo_705_);
lean_dec_ref(v_ctx_704_);
return v___x_729_;
}
}
v___jp_737_:
{
if (v___y_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___y_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__9));
v_a_728_ = v___x_740_;
goto v___jp_727_;
}
else
{
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v_expr_706_);
lean_dec_ref(v_toElabInfo_705_);
lean_dec_ref(v_ctx_704_);
return v___y_738_;
}
}
v___jp_741_:
{
uint8_t v___x_744_; 
v___x_744_ = l_Lean_Exception_isInterrupt(v_a_743_);
if (v___x_744_ == 0)
{
uint8_t v___x_745_; 
v___x_745_ = l_Lean_Exception_isRuntime(v_a_743_);
v___y_738_ = v___y_742_;
v___y_739_ = v___x_745_;
goto v___jp_737_;
}
else
{
lean_dec_ref(v_a_743_);
v___y_738_ = v___y_742_;
v___y_739_ = v___x_744_;
goto v___jp_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___lam__0___boxed(lean_object* v_ctx_759_, lean_object* v_toElabInfo_760_, lean_object* v_expr_761_, lean_object* v_isBinder_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
uint8_t v_isBinder_boxed_768_; lean_object* v_res_769_; 
v_isBinder_boxed_768_ = lean_unbox(v_isBinder_762_);
v_res_769_ = l_Lean_Elab_TermInfo_format___lam__0(v_ctx_759_, v_toElabInfo_760_, v_expr_761_, v_isBinder_boxed_768_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format(lean_object* v_ctx_770_, lean_object* v_info_771_){
_start:
{
lean_object* v_toElabInfo_773_; lean_object* v_expr_774_; uint8_t v_isBinder_775_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___x_778_; 
v_toElabInfo_773_ = lean_ctor_get(v_info_771_, 0);
v_expr_774_ = lean_ctor_get(v_info_771_, 3);
v_isBinder_775_ = lean_ctor_get_uint8(v_info_771_, sizeof(void*)*4);
v___x_776_ = lean_box(v_isBinder_775_);
lean_inc_ref(v_expr_774_);
lean_inc_ref(v_toElabInfo_773_);
lean_inc_ref(v_ctx_770_);
v___f_777_ = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_777_, 0, v_ctx_770_);
lean_closure_set(v___f_777_, 1, v_toElabInfo_773_);
lean_closure_set(v___f_777_, 2, v_expr_774_);
lean_closure_set(v___f_777_, 3, v___x_776_);
v___x_778_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_info_771_, v_ctx_770_, v___f_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TermInfo_format___boxed(lean_object* v_ctx_779_, lean_object* v_info_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Elab_TermInfo_format(v_ctx_779_, v_info_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialTermInfo_format(lean_object* v_ctx_786_, lean_object* v_info_787_){
_start:
{
lean_object* v_toElabInfo_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_toElabInfo_788_ = lean_ctor_get(v_info_787_, 0);
lean_inc_ref(v_toElabInfo_788_);
lean_dec_ref(v_info_787_);
v___x_789_ = ((lean_object*)(l_Lean_Elab_PartialTermInfo_format___closed__1));
v___x_790_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_786_, v_toElabInfo_788_);
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_799_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_810_; 
v_val_800_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_810_ == 0)
{
v___x_802_ = v_x_798_;
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v_x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_804_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_805_ = lean_expr_dbg_to_string(v_val_800_);
lean_dec(v_val_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 3);
lean_ctor_set(v___x_802_, 0, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_809_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_804_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0(lean_object* v_ctx_817_, lean_object* v_lctx_818_, lean_object* v_stx_819_, lean_object* v_expectedType_x3f_820_, lean_object* v_info_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_846_; 
v___x_827_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_817_, v_lctx_818_, v_stx_819_);
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_846_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_846_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_846_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_832_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__1));
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v_a_828_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_820_);
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_Lean_Elab_CompletionInfo_stx(v_info_821_);
v___x_841_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_817_, v___x_840_);
lean_dec(v___x_840_);
v___x_842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_839_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_842_);
v___x_844_ = v___x_830_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___lam__0___boxed(lean_object* v_ctx_847_, lean_object* v_lctx_848_, lean_object* v_stx_849_, lean_object* v_expectedType_x3f_850_, lean_object* v_info_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Elab_CompletionInfo_format___lam__0(v_ctx_847_, v_lctx_848_, v_stx_849_, v_expectedType_x3f_850_, v_info_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec_ref(v_info_851_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format(lean_object* v_ctx_864_, lean_object* v_info_865_){
_start:
{
switch(lean_obj_tag(v_info_865_))
{
case 0:
{
lean_object* v_termInfo_867_; lean_object* v_expectedType_x3f_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_889_; 
v_termInfo_867_ = lean_ctor_get(v_info_865_, 0);
v_expectedType_x3f_868_ = lean_ctor_get(v_info_865_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_info_865_);
if (v_isSharedCheck_889_ == 0)
{
v___x_870_ = v_info_865_;
v_isShared_871_ = v_isSharedCheck_889_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_expectedType_x3f_868_);
lean_inc(v_termInfo_867_);
lean_dec(v_info_865_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_889_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Elab_TermInfo_format(v_ctx_864_, v_termInfo_867_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_888_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_888_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_888_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_888_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__1));
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 5);
lean_ctor_set(v___x_870_, 1, v_a_873_);
lean_ctor_set(v___x_870_, 0, v___x_877_);
v___x_879_ = v___x_870_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_a_873_);
v___x_879_ = v_reuseFailAlloc_887_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_880_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0(v_expectedType_x3f_868_);
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_883_);
v___x_885_ = v___x_875_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_del_object(v___x_870_);
lean_dec(v_expectedType_x3f_868_);
return v___x_872_;
}
}
}
case 1:
{
lean_object* v_stx_890_; lean_object* v_lctx_891_; lean_object* v_expectedType_x3f_892_; lean_object* v___f_893_; lean_object* v___x_894_; 
v_stx_890_ = lean_ctor_get(v_info_865_, 0);
lean_inc(v_stx_890_);
v_lctx_891_ = lean_ctor_get(v_info_865_, 2);
lean_inc_ref_n(v_lctx_891_, 2);
v_expectedType_x3f_892_ = lean_ctor_get(v_info_865_, 3);
lean_inc(v_expectedType_x3f_892_);
lean_inc_ref(v_ctx_864_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Elab_CompletionInfo_format___lam__0___boxed), 10, 5);
lean_closure_set(v___f_893_, 0, v_ctx_864_);
lean_closure_set(v___f_893_, 1, v_lctx_891_);
lean_closure_set(v___f_893_, 2, v_stx_890_);
lean_closure_set(v___f_893_, 3, v_expectedType_x3f_892_);
lean_closure_set(v___f_893_, 4, v_info_865_);
v___x_894_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_864_, v_lctx_891_, v___f_893_);
return v___x_894_;
}
default: 
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_895_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___closed__3));
v___x_896_ = l_Lean_Elab_CompletionInfo_stx(v_info_865_);
lean_dec_ref(v_info_865_);
v___x_897_ = lean_box(0);
v___x_898_ = 0;
lean_inc(v___x_896_);
v___x_899_ = l_Lean_Syntax_formatStx(v___x_896_, v___x_897_, v___x_898_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_895_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_864_, v___x_896_);
lean_dec(v___x_896_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_format___boxed(lean_object* v_ctx_906_, lean_object* v_info_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Elab_CompletionInfo_format(v_ctx_906_, v_info_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format(lean_object* v_ctx_913_, lean_object* v_info_914_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_916_ = ((lean_object*)(l_Lean_Elab_CommandInfo_format___closed__1));
v___x_917_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_913_, v_info_914_);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandInfo_format___boxed(lean_object* v_ctx_920_, lean_object* v_info_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Elab_CommandInfo_format(v_ctx_920_, v_info_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format(lean_object* v_ctx_927_, lean_object* v_info_928_){
_start:
{
lean_object* v_stx_930_; lean_object* v_optionName_931_; lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_stx_930_ = lean_ctor_get(v_info_928_, 0);
lean_inc(v_stx_930_);
v_optionName_931_ = lean_ctor_get(v_info_928_, 1);
lean_inc(v_optionName_931_);
lean_dec_ref(v_info_928_);
v___x_932_ = ((lean_object*)(l_Lean_Elab_OptionInfo_format___closed__1));
v___x_933_ = 1;
v___x_934_ = l_Lean_Name_toString(v_optionName_931_, v___x_933_);
v___x_935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_932_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_927_, v_stx_930_);
lean_dec(v_stx_930_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OptionInfo_format___boxed(lean_object* v_ctx_942_, lean_object* v_info_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Elab_OptionInfo_format(v_ctx_942_, v_info_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format(lean_object* v_ctx_949_, lean_object* v_info_950_){
_start:
{
lean_object* v_stx_952_; lean_object* v_errorName_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_969_; 
v_stx_952_ = lean_ctor_get(v_info_950_, 0);
v_errorName_953_ = lean_ctor_get(v_info_950_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_info_950_);
if (v_isSharedCheck_969_ == 0)
{
v___x_955_ = v_info_950_;
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_errorName_953_);
lean_inc(v_stx_952_);
lean_dec(v_info_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_969_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_957_ = ((lean_object*)(l_Lean_Elab_ErrorNameInfo_format___closed__1));
v___x_958_ = 1;
v___x_959_ = l_Lean_Name_toString(v_errorName_953_, v___x_958_);
v___x_960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 5);
lean_ctor_set(v___x_955_, 1, v___x_960_);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_962_ = v___x_955_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_968_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_949_, v_stx_952_);
lean_dec(v_stx_952_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorNameInfo_format___boxed(lean_object* v_ctx_970_, lean_object* v_info_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_970_, v_info_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0(lean_object* v_val_980_, lean_object* v_fieldName_981_, lean_object* v_ctx_982_, lean_object* v_stx_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc_ref(v_val_980_);
v___x_989_ = lean_infer_type(v_val_980_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_Meta_ppExpr(v_a_990_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1022_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1022_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1022_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_ppExpr(v_val_980_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1021_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1021_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1021_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1001_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__1));
v___x_1002_ = 1;
v___x_1003_ = l_Lean_Name_toString(v_fieldName_981_, v___x_1002_);
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 3);
lean_ctor_set(v___x_994_, 0, v___x_1003_);
v___x_1005_ = v___x_994_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_CompletionInfo_format___lam__0___closed__3));
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v_a_992_);
v___x_1010_ = ((lean_object*)(l_Lean_Elab_FieldInfo_format___lam__0___closed__3));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_a_997_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_982_, v_stx_983_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1016_);
v___x_1018_ = v___x_999_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_del_object(v___x_994_);
lean_dec(v_a_992_);
lean_dec_ref(v_ctx_982_);
lean_dec(v_fieldName_981_);
return v___x_996_;
}
}
}
else
{
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec_ref(v_ctx_982_);
lean_dec(v_fieldName_981_);
lean_dec_ref(v_val_980_);
return v___x_991_;
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec_ref(v_ctx_982_);
lean_dec(v_fieldName_981_);
lean_dec_ref(v_val_980_);
v_a_1023_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_989_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_989_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___lam__0___boxed(lean_object* v_val_1031_, lean_object* v_fieldName_1032_, lean_object* v_ctx_1033_, lean_object* v_stx_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Elab_FieldInfo_format___lam__0(v_val_1031_, v_fieldName_1032_, v_ctx_1033_, v_stx_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v_stx_1034_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format(lean_object* v_ctx_1041_, lean_object* v_info_1042_){
_start:
{
lean_object* v_fieldName_1044_; lean_object* v_lctx_1045_; lean_object* v_val_1046_; lean_object* v_stx_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; 
v_fieldName_1044_ = lean_ctor_get(v_info_1042_, 1);
lean_inc(v_fieldName_1044_);
v_lctx_1045_ = lean_ctor_get(v_info_1042_, 2);
lean_inc_ref(v_lctx_1045_);
v_val_1046_ = lean_ctor_get(v_info_1042_, 3);
lean_inc_ref(v_val_1046_);
v_stx_1047_ = lean_ctor_get(v_info_1042_, 4);
lean_inc(v_stx_1047_);
lean_dec_ref(v_info_1042_);
lean_inc_ref(v_ctx_1041_);
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1048_, 0, v_val_1046_);
lean_closure_set(v___f_1048_, 1, v_fieldName_1044_);
lean_closure_set(v___f_1048_, 2, v_ctx_1041_);
lean_closure_set(v___f_1048_, 3, v_stx_1047_);
v___x_1049_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1041_, v_lctx_1045_, v___f_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldInfo_format___boxed(lean_object* v_ctx_1050_, lean_object* v_info_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Elab_FieldInfo_format(v_ctx_1050_, v_info_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(lean_object* v_pre_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_dec(v_pre_1054_);
return v_x_1055_;
}
else
{
lean_object* v_head_1057_; lean_object* v_tail_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1067_; 
v_head_1057_ = lean_ctor_get(v_x_1056_, 0);
v_tail_1058_ = lean_ctor_get(v_x_1056_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1060_ = v_x_1056_;
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_tail_1058_);
lean_inc(v_head_1057_);
lean_dec(v_x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
lean_inc(v_pre_1054_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 5);
lean_ctor_set(v___x_1060_, 1, v_pre_1054_);
lean_ctor_set(v___x_1060_, 0, v_x_1055_);
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_x_1055_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_pre_1054_);
v___x_1063_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_head_1057_);
v_x_1055_ = v___x_1064_;
v_x_1056_ = v_tail_1058_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(lean_object* v_pre_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 0)
{
lean_object* v___x_1070_; 
lean_dec(v_pre_1068_);
v___x_1070_ = lean_box(0);
return v___x_1070_;
}
else
{
lean_object* v_head_1071_; lean_object* v_tail_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1080_; 
v_head_1071_ = lean_ctor_get(v_x_1069_, 0);
v_tail_1072_ = lean_ctor_get(v_x_1069_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_x_1069_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1074_ = v_x_1069_;
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_tail_1072_);
lean_inc(v_head_1071_);
lean_dec(v_x_1069_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
lean_inc(v_pre_1068_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 5);
lean_ctor_set(v___x_1074_, 1, v_head_1071_);
lean_ctor_set(v___x_1074_, 0, v_pre_1068_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_pre_1068_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_head_1071_);
v___x_1077_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_List_foldl___at___00Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1_spec__1(v_pre_1068_, v___x_1077_, v_tail_1072_);
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = l_List_reverse___redArg(v_x_1082_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
else
{
lean_object* v_head_1090_; lean_object* v_tail_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1109_; 
v_head_1090_ = lean_ctor_get(v_x_1081_, 0);
v_tail_1091_ = lean_ctor_get(v_x_1081_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_1081_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1093_ = v_x_1081_;
v_isShared_1094_ = v_isSharedCheck_1109_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_tail_1091_);
lean_inc(v_head_1090_);
lean_dec(v_x_1081_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1109_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Meta_ppGoal(v_head_1090_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v_head_1090_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_x_1082_);
lean_ctor_set(v___x_1093_, 0, v_a_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1096_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_x_1082_);
v___x_1098_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v_x_1081_ = v_tail_1091_;
v_x_1082_ = v___x_1098_;
goto _start;
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_del_object(v___x_1093_);
lean_dec(v_tail_1091_);
lean_dec(v_x_1082_);
v_a_1101_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1095_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1095_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0___boxed(lean_object* v_x_1110_, lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_x_1110_, v_x_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0(lean_object* v_goals_1121_, lean_object* v___x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_List_mapM_loop___at___00Lean_Elab_ContextInfo_ppGoals_spec__0(v_goals_1121_, v___x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1138_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1133_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1134_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1133_, v_a_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_a_1139_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1128_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1128_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed(lean_object* v_goals_1147_, lean_object* v___x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Elab_ContextInfo_ppGoals___lam__0(v_goals_1147_, v___x_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1154_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0(void){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__0, &l_Lean_Elab_ContextInfo_ppGoals___closed__0_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__0);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(32u);
v___x_1159_ = lean_mk_empty_array_with_capacity(v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3(void){
_start:
{
size_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1161_ = ((size_t)5ULL);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_unsigned_to_nat(32u);
v___x_1164_ = lean_mk_empty_array_with_capacity(v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__2, &l_Lean_Elab_ContextInfo_ppGoals___closed__2_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2);
v___x_1166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___x_1164_);
lean_ctor_set(v___x_1166_, 2, v___x_1162_);
lean_ctor_set(v___x_1166_, 3, v___x_1162_);
lean_ctor_set_usize(v___x_1166_, 4, v___x_1161_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1167_ = lean_box(1);
v___x_1168_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_1169_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__1, &l_Lean_Elab_ContextInfo_ppGoals___closed__1_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1);
v___x_1170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1168_);
lean_ctor_set(v___x_1170_, 2, v___x_1167_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* v_ctx_1174_, lean_object* v_goals_1175_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = l_List_isEmpty___redArg(v_goals_1175_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; 
v___x_1178_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__4, &l_Lean_Elab_ContextInfo_ppGoals___closed__4_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__4);
v___x_1179_ = lean_box(0);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1180_, 0, v_goals_1175_);
lean_closure_set(v___f_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1174_, v___x_1178_, v___f_1180_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_goals_1175_);
lean_dec_ref(v_ctx_1174_);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___closed__6));
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* v_ctx_1184_, lean_object* v_goals_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctx_1184_, v_goals_1185_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format(lean_object* v_ctx_1197_, lean_object* v_info_1198_){
_start:
{
lean_object* v_toCommandContextInfo_1200_; lean_object* v_parentDecl_x3f_1201_; lean_object* v_autoImplicits_1202_; lean_object* v_env_1203_; lean_object* v_cmdEnv_x3f_1204_; lean_object* v_fileMap_1205_; lean_object* v_options_1206_; lean_object* v_currNamespace_1207_; lean_object* v_openDecls_1208_; lean_object* v_ngen_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1251_; 
v_toCommandContextInfo_1200_ = lean_ctor_get(v_ctx_1197_, 0);
lean_inc_ref(v_toCommandContextInfo_1200_);
v_parentDecl_x3f_1201_ = lean_ctor_get(v_ctx_1197_, 1);
v_autoImplicits_1202_ = lean_ctor_get(v_ctx_1197_, 2);
v_env_1203_ = lean_ctor_get(v_toCommandContextInfo_1200_, 0);
v_cmdEnv_x3f_1204_ = lean_ctor_get(v_toCommandContextInfo_1200_, 1);
v_fileMap_1205_ = lean_ctor_get(v_toCommandContextInfo_1200_, 2);
v_options_1206_ = lean_ctor_get(v_toCommandContextInfo_1200_, 4);
v_currNamespace_1207_ = lean_ctor_get(v_toCommandContextInfo_1200_, 5);
v_openDecls_1208_ = lean_ctor_get(v_toCommandContextInfo_1200_, 6);
v_ngen_1209_ = lean_ctor_get(v_toCommandContextInfo_1200_, 7);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_toCommandContextInfo_1200_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v_toCommandContextInfo_1200_, 3);
lean_dec(v_unused_1252_);
v___x_1211_ = v_toCommandContextInfo_1200_;
v_isShared_1212_ = v_isSharedCheck_1251_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_ngen_1209_);
lean_inc(v_openDecls_1208_);
lean_inc(v_currNamespace_1207_);
lean_inc(v_options_1206_);
lean_inc(v_fileMap_1205_);
lean_inc(v_cmdEnv_x3f_1204_);
lean_inc(v_env_1203_);
lean_dec(v_toCommandContextInfo_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1251_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_toElabInfo_1213_; lean_object* v_mctxBefore_1214_; lean_object* v_goalsBefore_1215_; lean_object* v_mctxAfter_1216_; lean_object* v_goalsAfter_1217_; lean_object* v___x_1219_; 
v_toElabInfo_1213_ = lean_ctor_get(v_info_1198_, 0);
lean_inc_ref(v_toElabInfo_1213_);
v_mctxBefore_1214_ = lean_ctor_get(v_info_1198_, 1);
lean_inc_ref(v_mctxBefore_1214_);
v_goalsBefore_1215_ = lean_ctor_get(v_info_1198_, 2);
lean_inc(v_goalsBefore_1215_);
v_mctxAfter_1216_ = lean_ctor_get(v_info_1198_, 3);
lean_inc_ref(v_mctxAfter_1216_);
v_goalsAfter_1217_ = lean_ctor_get(v_info_1198_, 4);
lean_inc(v_goalsAfter_1217_);
lean_dec_ref(v_info_1198_);
lean_inc_ref(v_ngen_1209_);
lean_inc(v_openDecls_1208_);
lean_inc(v_currNamespace_1207_);
lean_inc_ref(v_options_1206_);
lean_inc_ref(v_fileMap_1205_);
lean_inc(v_cmdEnv_x3f_1204_);
lean_inc_ref(v_env_1203_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 3, v_mctxBefore_1214_);
v___x_1219_ = v___x_1211_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_env_1203_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_cmdEnv_x3f_1204_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_fileMap_1205_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_mctxBefore_1214_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_options_1206_);
lean_ctor_set(v_reuseFailAlloc_1250_, 5, v_currNamespace_1207_);
lean_ctor_set(v_reuseFailAlloc_1250_, 6, v_openDecls_1208_);
lean_ctor_set(v_reuseFailAlloc_1250_, 7, v_ngen_1209_);
v___x_1219_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v_ctxB_1220_; lean_object* v___x_1221_; 
lean_inc_ref(v_autoImplicits_1202_);
lean_inc(v_parentDecl_x3f_1201_);
v_ctxB_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxB_1220_, 0, v___x_1219_);
lean_ctor_set(v_ctxB_1220_, 1, v_parentDecl_x3f_1201_);
lean_ctor_set(v_ctxB_1220_, 2, v_autoImplicits_1202_);
v___x_1221_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxB_1220_, v_goalsBefore_1215_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1223_; lean_object* v_ctxA_1224_; lean_object* v___x_1225_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1223_, 0, v_env_1203_);
lean_ctor_set(v___x_1223_, 1, v_cmdEnv_x3f_1204_);
lean_ctor_set(v___x_1223_, 2, v_fileMap_1205_);
lean_ctor_set(v___x_1223_, 3, v_mctxAfter_1216_);
lean_ctor_set(v___x_1223_, 4, v_options_1206_);
lean_ctor_set(v___x_1223_, 5, v_currNamespace_1207_);
lean_ctor_set(v___x_1223_, 6, v_openDecls_1208_);
lean_ctor_set(v___x_1223_, 7, v_ngen_1209_);
lean_inc_ref(v_autoImplicits_1202_);
lean_inc(v_parentDecl_x3f_1201_);
v_ctxA_1224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_ctxA_1224_, 0, v___x_1223_);
lean_ctor_set(v_ctxA_1224_, 1, v_parentDecl_x3f_1201_);
lean_ctor_set(v_ctxA_1224_, 2, v_autoImplicits_1202_);
v___x_1225_ = l_Lean_Elab_ContextInfo_ppGoals(v_ctxA_1224_, v_goalsAfter_1217_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1249_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1249_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1249_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_stx_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v_stx_1230_ = lean_ctor_get(v_toElabInfo_1213_, 1);
lean_inc(v_stx_1230_);
v___x_1231_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__1));
v___x_1232_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1197_, v_toElabInfo_1213_);
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
v___x_1235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = lean_box(0);
v___x_1237_ = 0;
v___x_1238_ = l_Lean_Syntax_formatStx(v_stx_1230_, v___x_1236_, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1235_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__3));
v___x_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1222_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_TacticInfo_format___closed__5));
v___x_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v_a_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1245_);
v___x_1247_ = v___x_1228_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_dec(v_a_1222_);
lean_dec_ref(v_toElabInfo_1213_);
lean_dec_ref(v_ctx_1197_);
return v___x_1225_;
}
}
else
{
lean_dec(v_goalsAfter_1217_);
lean_dec_ref(v_mctxAfter_1216_);
lean_dec_ref(v_toElabInfo_1213_);
lean_dec_ref(v_ngen_1209_);
lean_dec(v_openDecls_1208_);
lean_dec(v_currNamespace_1207_);
lean_dec_ref(v_options_1206_);
lean_dec_ref(v_fileMap_1205_);
lean_dec(v_cmdEnv_x3f_1204_);
lean_dec_ref(v_env_1203_);
lean_dec_ref(v_ctx_1197_);
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TacticInfo_format___boxed(lean_object* v_ctx_1253_, lean_object* v_info_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_Elab_TacticInfo_format(v_ctx_1253_, v_info_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* v_ctx_1263_, lean_object* v_info_1264_){
_start:
{
lean_object* v_lctx_1266_; lean_object* v_stx_1267_; lean_object* v_output_1268_; lean_object* v___x_1269_; lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1284_; 
v_lctx_1266_ = lean_ctor_get(v_info_1264_, 0);
lean_inc_ref_n(v_lctx_1266_, 2);
v_stx_1267_ = lean_ctor_get(v_info_1264_, 1);
lean_inc(v_stx_1267_);
v_output_1268_ = lean_ctor_get(v_info_1264_, 2);
lean_inc(v_output_1268_);
lean_dec_ref(v_info_1264_);
v___x_1269_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1263_, v_lctx_1266_, v_stx_1267_);
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = l_Lean_Elab_ContextInfo_ppSyntax(v_ctx_1263_, v_lctx_1266_, v_output_1268_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1284_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1276_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__1));
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_a_1270_);
v___x_1278_ = ((lean_object*)(l_Lean_Elab_MacroExpansionInfo_format___closed__3));
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1280_);
v___x_1282_ = v___x_1274_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* v_ctx_1285_, lean_object* v_info_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1285_, v_info_1286_);
lean_dec_ref(v_ctx_1285_);
return v_res_1288_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__0(void){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__1(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__0, &l_Lean_Elab_UserWidgetInfo_format___closed__0_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__0);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_Elab_UserWidgetInfo_format___closed__2(void){
_start:
{
uint8_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = 1;
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__1, &l_Lean_Elab_UserWidgetInfo_format___closed__1_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__1);
v___x_1295_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
lean_ctor_set_usize(v___x_1295_, 2, v___x_1293_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*3, v___x_1292_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_UserWidgetInfo_format(lean_object* v_info_1299_){
_start:
{
lean_object* v_toWidgetInstance_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1329_; 
v_toWidgetInstance_1300_ = lean_ctor_get(v_info_1299_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_info_1299_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_info_1299_, 1);
lean_dec(v_unused_1330_);
v___x_1302_ = v_info_1299_;
v_isShared_1303_ = v_isSharedCheck_1329_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_toWidgetInstance_1300_);
lean_dec(v_info_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1329_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_id_1304_; lean_object* v_props_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_fst_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1327_; 
v_id_1304_ = lean_ctor_get(v_toWidgetInstance_1300_, 0);
lean_inc(v_id_1304_);
v_props_1305_ = lean_ctor_get(v_toWidgetInstance_1300_, 1);
lean_inc_ref(v_props_1305_);
lean_dec_ref(v_toWidgetInstance_1300_);
v___x_1306_ = lean_obj_once(&l_Lean_Elab_UserWidgetInfo_format___closed__2, &l_Lean_Elab_UserWidgetInfo_format___closed__2_once, _init_l_Lean_Elab_UserWidgetInfo_format___closed__2);
v___x_1307_ = lean_apply_1(v_props_1305_, v___x_1306_);
v_fst_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v___x_1307_, 1);
lean_dec(v_unused_1328_);
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1327_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_fst_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1327_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1312_ = ((lean_object*)(l_Lean_Elab_UserWidgetInfo_format___closed__4));
v___x_1313_ = 1;
v___x_1314_ = l_Lean_Name_toString(v_id_1304_, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 5);
lean_ctor_set(v___x_1310_, 1, v___x_1315_);
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1317_ = v___x_1310_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_ContextInfo_ppGoals___lam__0___closed__1));
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 5);
lean_ctor_set(v___x_1302_, 1, v___x_1318_);
lean_ctor_set(v___x_1302_, 0, v___x_1317_);
v___x_1320_ = v___x_1302_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_unsigned_to_nat(80u);
v___x_1322_ = l_Lean_Json_pretty(v_fst_1308_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1320_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FVarAliasInfo_format(lean_object* v_info_1337_){
_start:
{
lean_object* v_userName_1338_; lean_object* v_id_1339_; lean_object* v_baseId_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_userName_1338_ = lean_ctor_get(v_info_1337_, 0);
lean_inc(v_userName_1338_);
v_id_1339_ = lean_ctor_get(v_info_1337_, 1);
lean_inc(v_id_1339_);
v_baseId_1340_ = lean_ctor_get(v_info_1337_, 2);
lean_inc(v_baseId_1340_);
lean_dec_ref(v_info_1337_);
v___x_1341_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__1));
v___x_1342_ = l_Lean_Name_eraseMacroScopes(v_userName_1338_);
lean_dec(v_userName_1338_);
v___x_1343_ = 1;
v___x_1344_ = l_Lean_Name_toString(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1341_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__1));
v___x_1348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_Name_toString(v_id_1339_, v___x_1343_);
v___x_1350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1348_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Lean_Elab_FVarAliasInfo_format___closed__3));
v___x_1353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_Name_toString(v_baseId_1340_, v___x_1343_);
v___x_1355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1353_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format(lean_object* v_ctx_1360_, lean_object* v_info_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((lean_object*)(l_Lean_Elab_FieldRedeclInfo_format___closed__1));
v___x_1363_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1360_, v_info_1361_);
v___x_1364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FieldRedeclInfo_format___boxed(lean_object* v_ctx_1365_, lean_object* v_info_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1365_, v_info_1366_);
lean_dec(v_info_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f(lean_object* v_ppCtx_1370_, lean_object* v_info_1371_){
_start:
{
lean_object* v_mkDocString_x3f_1373_; 
v_mkDocString_x3f_1373_ = lean_ctor_get(v_info_1371_, 2);
lean_inc(v_mkDocString_x3f_1373_);
lean_dec_ref(v_info_1371_);
if (lean_obj_tag(v_mkDocString_x3f_1373_) == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref(v_ppCtx_1370_);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
else
{
lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1408_; 
v_val_1376_ = lean_ctor_get(v_mkDocString_x3f_1373_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_mkDocString_x3f_1373_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1378_ = v_mkDocString_x3f_1373_;
v_isShared_1379_ = v_isSharedCheck_1408_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_dec(v_mkDocString_x3f_1373_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1408_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_apply_2(v_val_1376_, v_ppCtx_1370_, lean_box(0));
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_a_1381_);
v___x_1386_ = v___x_1378_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1386_);
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1407_; 
v_a_1392_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1394_ = v___x_1380_;
v_isShared_1395_ = v_isSharedCheck_1407_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1380_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1407_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1396_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__0));
v___x_1397_ = lean_io_error_to_string(v_a_1392_);
v___x_1398_ = lean_string_append(v___x_1396_, v___x_1397_);
lean_dec_ref(v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1400_ = lean_string_append(v___x_1398_, v___x_1399_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1400_);
v___x_1402_ = v___x_1378_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1402_);
v___x_1404_ = v___x_1394_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_docString_x3f___boxed(lean_object* v_ppCtx_1409_, lean_object* v_info_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v_ppCtx_1409_, v_info_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v___x_1415_; 
v___x_1415_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
return v___x_1415_;
}
else
{
lean_object* v_val_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1427_; 
v_val_1416_ = lean_ctor_get(v_x_1413_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1418_ = v_x_1413_;
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_val_1416_);
lean_dec(v_x_1413_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1420_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__3));
v___x_1421_ = l_String_quote(v_val_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 3);
lean_ctor_set(v___x_1418_, 0, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1420_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = l_Repr_addAppParen(v___x_1424_, v_x_1414_);
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0___boxed(lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_x_1428_, v_x_1429_);
lean_dec(v_x_1429_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format(lean_object* v_ctx_1445_, lean_object* v_info_1446_){
_start:
{
lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v_toTermInfo_1454_; lean_object* v_location_x3f_1455_; uint8_t v_explicit_1456_; lean_object* v___y_1458_; 
v_toTermInfo_1454_ = lean_ctor_get(v_info_1446_, 0);
lean_inc_ref(v_toTermInfo_1454_);
v_location_x3f_1455_ = lean_ctor_get(v_info_1446_, 1);
lean_inc(v_location_x3f_1455_);
v_explicit_1456_ = lean_ctor_get_uint8(v_info_1446_, sizeof(void*)*3);
if (lean_obj_tag(v_location_x3f_1455_) == 1)
{
lean_object* v_val_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1540_; 
v_val_1479_ = lean_ctor_get(v_location_x3f_1455_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_location_x3f_1455_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1481_ = v_location_x3f_1455_;
v_isShared_1482_ = v_isSharedCheck_1540_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_val_1479_);
lean_dec(v_location_x3f_1455_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1540_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_range_1483_; lean_object* v_pos_1484_; lean_object* v_endPos_1485_; lean_object* v_module_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1538_; 
v_range_1483_ = lean_ctor_get(v_val_1479_, 1);
v_pos_1484_ = lean_ctor_get(v_range_1483_, 0);
lean_inc_ref(v_pos_1484_);
v_endPos_1485_ = lean_ctor_get(v_range_1483_, 2);
lean_inc_ref(v_endPos_1485_);
v_module_1486_ = lean_ctor_get(v_val_1479_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_val_1479_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_val_1479_, 1);
lean_dec(v_unused_1539_);
v___x_1488_ = v_val_1479_;
v_isShared_1489_ = v_isSharedCheck_1538_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_module_1486_);
lean_dec(v_val_1479_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1538_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_line_1490_; lean_object* v_column_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1537_; 
v_line_1490_ = lean_ctor_get(v_pos_1484_, 0);
v_column_1491_ = lean_ctor_get(v_pos_1484_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_pos_1484_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1493_ = v_pos_1484_;
v_isShared_1494_ = v_isSharedCheck_1537_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_column_1491_);
lean_inc(v_line_1490_);
lean_dec(v_pos_1484_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1537_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_line_1495_; lean_object* v_column_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1536_; 
v_line_1495_ = lean_ctor_get(v_endPos_1485_, 0);
v_column_1496_ = lean_ctor_get(v_endPos_1485_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_endPos_1485_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1498_ = v_endPos_1485_;
v_isShared_1499_ = v_isSharedCheck_1536_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_column_1496_);
lean_inc(v_line_1495_);
lean_dec(v_endPos_1485_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1536_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = 1;
v___x_1501_ = l_Lean_Name_toString(v_module_1486_, v___x_1500_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 3);
lean_ctor_set(v___x_1481_, 0, v___x_1501_);
v___x_1503_ = v___x_1481_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = ((lean_object*)(l_Lean_Elab_TermInfo_format___lam__0___closed__5));
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 5);
lean_ctor_set(v___x_1498_, 1, v___x_1504_);
lean_ctor_set(v___x_1498_, 0, v___x_1503_);
v___x_1506_ = v___x_1498_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__1));
v___x_1508_ = l_Nat_reprFast(v_line_1490_);
v___x_1509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set_tag(v___x_1493_, 5);
lean_ctor_set(v___x_1493_, 1, v___x_1509_);
lean_ctor_set(v___x_1493_, 0, v___x_1507_);
v___x_1511_ = v___x_1493_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__3));
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 5);
lean_ctor_set(v___x_1488_, 1, v___x_1512_);
lean_ctor_set(v___x_1488_, 0, v___x_1511_);
v___x_1514_ = v___x_1488_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1515_ = l_Nat_reprFast(v_column_1491_);
v___x_1516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1514_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__5));
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1506_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange___closed__1));
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = l_Nat_reprFast(v_line_1495_);
v___x_1524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1507_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1512_);
v___x_1527_ = l_Nat_reprFast(v_column_1496_);
v___x_1528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1526_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1518_);
v___x_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1522_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___y_1458_ = v___x_1531_;
goto v___jp_1457_;
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
lean_object* v___x_1541_; 
lean_dec(v_location_x3f_1455_);
v___x_1541_ = ((lean_object*)(l_Option_format___at___00Lean_Elab_CompletionInfo_format_spec__0___closed__1));
v___y_1458_ = v___x_1541_;
goto v___jp_1457_;
}
v___jp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_inc_ref(v___y_1450_);
v___x_1451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1450_);
v___x_1452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___y_1449_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
v___jp_1457_:
{
lean_object* v_lctx_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_lctx_1459_ = lean_ctor_get(v_toTermInfo_1454_, 1);
lean_inc_ref(v_lctx_1459_);
v___x_1460_ = l_Lean_Elab_ContextInfo_toPPContext(v_ctx_1445_, v_lctx_1459_);
v___x_1461_ = l_Lean_Elab_DelabTermInfo_docString_x3f(v___x_1460_, v_info_1446_);
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = l_Lean_Elab_TermInfo_format(v_ctx_1445_, v_toTermInfo_1454_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__1));
v___x_1466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v_a_1464_);
v___x_1467_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__3));
v___x_1468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v___y_1458_);
v___x_1470_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__5));
v___x_1471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = l_Option_repr___at___00Lean_Elab_DelabTermInfo_format_spec__0(v_a_1462_, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1471_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__7));
v___x_1476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
if (v_explicit_1456_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__8));
v___y_1449_ = v___x_1476_;
v___y_1450_ = v___x_1477_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1478_; 
v___x_1478_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_format___closed__9));
v___y_1449_ = v___x_1476_;
v___y_1450_ = v___x_1478_;
goto v___jp_1448_;
}
}
else
{
lean_dec(v_a_1462_);
lean_dec(v___y_1458_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DelabTermInfo_format___boxed(lean_object* v_ctx_1542_, lean_object* v_info_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1542_, v_info_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceInfo_format(lean_object* v_ctx_1549_, lean_object* v_info_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = ((lean_object*)(l_Lean_Elab_ChoiceInfo_format___closed__1));
v___x_1552_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1549_, v_info_1550_);
v___x_1553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ChoiceResolutionInfo_format(lean_object* v_ctx_1566_, lean_object* v_info_1567_){
_start:
{
lean_object* v_stx_1568_; lean_object* v_chosenAltIdx_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1597_; 
v_stx_1568_ = lean_ctor_get(v_info_1567_, 0);
v_chosenAltIdx_1569_ = lean_ctor_get(v_info_1567_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_info_1567_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1571_ = v_info_1567_;
v_isShared_1572_ = v_isSharedCheck_1597_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_chosenAltIdx_1569_);
lean_inc(v_stx_1568_);
lean_dec(v_info_1567_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1597_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1573_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__1));
lean_inc(v_chosenAltIdx_1569_);
v___x_1574_ = l_Nat_reprFast(v_chosenAltIdx_1569_);
v___x_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 5);
lean_ctor_set(v___x_1571_, 1, v___x_1575_);
lean_ctor_set(v___x_1571_, 0, v___x_1573_);
v___x_1577_ = v___x_1571_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1578_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__3));
v___x_1579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = l_Lean_Syntax_getNumArgs(v_stx_1568_);
v___x_1581_ = l_Nat_reprFast(v___x_1580_);
v___x_1582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1579_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = l_Lean_Syntax_getArg(v_stx_1568_, v_chosenAltIdx_1569_);
lean_dec(v_chosenAltIdx_1569_);
v___x_1587_ = l_Lean_Syntax_getKind(v___x_1586_);
v___x_1588_ = 1;
v___x_1589_ = l_Lean_Name_toString(v___x_1587_, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1585_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange(v_ctx_1566_, v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_1595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
return v___x_1595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocInfo_format(lean_object* v_ctx_1601_, lean_object* v_info_1602_){
_start:
{
lean_object* v_stx_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_stx_1603_ = lean_ctor_get(v_info_1602_, 1);
v___x_1604_ = ((lean_object*)(l_Lean_Elab_DocInfo_format___closed__1));
lean_inc(v_stx_1603_);
v___x_1605_ = l_Lean_Syntax_getKind(v_stx_1603_);
v___x_1606_ = 1;
v___x_1607_ = l_Lean_Name_toString(v___x_1605_, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1604_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo___closed__1));
v___x_1611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1601_, v_info_1602_);
v___x_1613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DocElabInfo_format(lean_object* v_ctx_1617_, lean_object* v_info_1618_){
_start:
{
lean_object* v_toElabInfo_1619_; lean_object* v_name_1620_; uint8_t v_kind_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_toElabInfo_1619_ = lean_ctor_get(v_info_1618_, 0);
lean_inc_ref(v_toElabInfo_1619_);
v_name_1620_ = lean_ctor_get(v_info_1618_, 1);
lean_inc(v_name_1620_);
v_kind_1621_ = lean_ctor_get_uint8(v_info_1618_, sizeof(void*)*2);
lean_dec_ref(v_info_1618_);
v___x_1622_ = ((lean_object*)(l_Lean_Elab_DocElabInfo_format___closed__1));
v___x_1623_ = 1;
v___x_1624_ = l_Lean_Name_toString(v_name_1620_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___x_1626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1622_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__5));
v___x_1628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = l_Lean_Elab_instReprDocElabKind_repr(v_kind_1621_, v___x_1629_);
v___x_1631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1628_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = ((lean_object*)(l_Lean_Elab_ChoiceResolutionInfo_format___closed__7));
v___x_1633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatElabInfo(v_ctx_1617_, v_toElabInfo_1619_);
v___x_1635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format(lean_object* v_ctx_1636_, lean_object* v_x_1637_){
_start:
{
switch(lean_obj_tag(v_x_1637_))
{
case 0:
{
lean_object* v_i_1639_; lean_object* v___x_1640_; 
v_i_1639_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1639_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1640_ = l_Lean_Elab_TacticInfo_format(v_ctx_1636_, v_i_1639_);
return v___x_1640_;
}
case 1:
{
lean_object* v_i_1641_; lean_object* v___x_1642_; 
v_i_1641_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1641_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1642_ = l_Lean_Elab_TermInfo_format(v_ctx_1636_, v_i_1641_);
return v___x_1642_;
}
case 2:
{
lean_object* v_i_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
v_i_1643_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1645_ = v_x_1637_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_i_1643_);
lean_dec(v_x_1637_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = l_Lean_Elab_PartialTermInfo_format(v_ctx_1636_, v_i_1643_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
case 3:
{
lean_object* v_i_1652_; lean_object* v___x_1653_; 
v_i_1652_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1652_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1653_ = l_Lean_Elab_CommandInfo_format(v_ctx_1636_, v_i_1652_);
return v___x_1653_;
}
case 4:
{
lean_object* v_i_1654_; lean_object* v___x_1655_; 
v_i_1654_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1654_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1655_ = l_Lean_Elab_MacroExpansionInfo_format(v_ctx_1636_, v_i_1654_);
lean_dec_ref(v_ctx_1636_);
return v___x_1655_;
}
case 5:
{
lean_object* v_i_1656_; lean_object* v___x_1657_; 
v_i_1656_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1656_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1657_ = l_Lean_Elab_OptionInfo_format(v_ctx_1636_, v_i_1656_);
return v___x_1657_;
}
case 6:
{
lean_object* v_i_1658_; lean_object* v___x_1659_; 
v_i_1658_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1658_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1659_ = l_Lean_Elab_ErrorNameInfo_format(v_ctx_1636_, v_i_1658_);
return v___x_1659_;
}
case 7:
{
lean_object* v_i_1660_; lean_object* v___x_1661_; 
v_i_1660_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1660_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1661_ = l_Lean_Elab_FieldInfo_format(v_ctx_1636_, v_i_1660_);
return v___x_1661_;
}
case 8:
{
lean_object* v_i_1662_; lean_object* v___x_1663_; 
v_i_1662_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1662_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1663_ = l_Lean_Elab_CompletionInfo_format(v_ctx_1636_, v_i_1662_);
return v___x_1663_;
}
case 9:
{
lean_object* v_i_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v_ctx_1636_);
v_i_1664_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v_x_1637_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_i_1664_);
lean_dec(v_x_1637_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lean_Elab_UserWidgetInfo_format(v_i_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
case 10:
{
lean_object* v_i_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v_ctx_1636_);
v_i_1673_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1675_ = v_x_1637_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_i_1673_);
lean_dec(v_x_1637_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = l_Lean_Elab_CustomInfo_format(v_i_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set_tag(v___x_1675_, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
case 11:
{
lean_object* v_i_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_ctx_1636_);
v_i_1682_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1684_ = v_x_1637_;
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_i_1682_);
lean_dec(v_x_1637_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = l_Lean_Elab_FVarAliasInfo_format(v_i_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
case 12:
{
lean_object* v_i_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_i_1691_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1693_ = v_x_1637_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_i_1691_);
lean_dec(v_x_1637_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = l_Lean_Elab_FieldRedeclInfo_format(v_ctx_1636_, v_i_1691_);
lean_dec(v_i_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
case 13:
{
lean_object* v_i_1700_; lean_object* v___x_1701_; 
v_i_1700_ = lean_ctor_get(v_x_1637_, 0);
lean_inc_ref(v_i_1700_);
lean_dec_ref_known(v_x_1637_, 1);
v___x_1701_ = l_Lean_Elab_DelabTermInfo_format(v_ctx_1636_, v_i_1700_);
return v___x_1701_;
}
case 14:
{
lean_object* v_i_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_i_1702_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1704_ = v_x_1637_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_i_1702_);
lean_dec(v_x_1637_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = l_Lean_Elab_ChoiceInfo_format(v_ctx_1636_, v_i_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set_tag(v___x_1704_, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
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
case 15:
{
lean_object* v_i_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1719_; 
v_i_1711_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1713_ = v_x_1637_;
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_i_1711_);
lean_dec(v_x_1637_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = l_Lean_Elab_ChoiceResolutionInfo_format(v_ctx_1636_, v_i_1711_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1715_);
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
case 16:
{
lean_object* v_i_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1728_; 
v_i_1720_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1722_ = v_x_1637_;
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_i_1720_);
lean_dec(v_x_1637_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = l_Lean_Elab_DocInfo_format(v_ctx_1636_, v_i_1720_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1724_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
default: 
{
lean_object* v_i_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_i_1729_ = lean_ctor_get(v_x_1637_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v_x_1637_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_i_1729_);
lean_dec(v_x_1637_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = l_Lean_Elab_DocElabInfo_format(v_ctx_1636_, v_i_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set_tag(v___x_1731_, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_format___boxed(lean_object* v_ctx_1738_, lean_object* v_x_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Elab_Info_format(v_ctx_1738_, v_x_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
if (lean_obj_tag(v_x_1743_) == 0)
{
return v_x_1742_;
}
else
{
lean_object* v_head_1744_; lean_object* v_tail_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_head_1744_ = lean_ctor_get(v_x_1743_, 0);
v_tail_1745_ = lean_ctor_get(v_x_1743_, 1);
v___x_1746_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_formatStxRange_fmtPos___closed__2));
v___x_1747_ = lean_string_append(v_x_1742_, v___x_1746_);
v___x_1748_ = lean_expr_dbg_to_string(v_head_1744_);
v___x_1749_ = lean_string_append(v___x_1747_, v___x_1748_);
lean_dec_ref(v___x_1748_);
v_x_1742_ = v___x_1749_;
v_x_1743_ = v_tail_1745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0___boxed(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v_x_1751_, v_x_1752_);
lean_dec(v_x_1752_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(lean_object* v_x_1756_){
_start:
{
if (lean_obj_tag(v_x_1756_) == 0)
{
lean_object* v___x_1757_; 
v___x_1757_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__0));
return v___x_1757_;
}
else
{
lean_object* v_tail_1758_; 
v_tail_1758_ = lean_ctor_get(v_x_1756_, 1);
if (lean_obj_tag(v_tail_1758_) == 0)
{
lean_object* v_head_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_head_1759_ = lean_ctor_get(v_x_1756_, 0);
v___x_1760_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1761_ = lean_expr_dbg_to_string(v_head_1759_);
v___x_1762_ = lean_string_append(v___x_1760_, v___x_1761_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1764_ = lean_string_append(v___x_1762_, v___x_1763_);
return v___x_1764_;
}
else
{
lean_object* v_head_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; uint32_t v___x_1770_; lean_object* v___x_1771_; 
v_head_1765_ = lean_ctor_get(v_x_1756_, 0);
v___x_1766_ = ((lean_object*)(l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___closed__1));
v___x_1767_ = lean_expr_dbg_to_string(v_head_1765_);
v___x_1768_ = lean_string_append(v___x_1766_, v___x_1767_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = l_List_foldl___at___00List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0_spec__0(v___x_1768_, v_tail_1758_);
v___x_1770_ = 93;
v___x_1771_ = lean_string_push(v___x_1769_, v___x_1770_);
return v___x_1771_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0___boxed(lean_object* v_x_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v_x_1772_);
lean_dec(v_x_1772_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_format(lean_object* v_ctx_1780_){
_start:
{
switch(lean_obj_tag(v_ctx_1780_))
{
case 0:
{
lean_object* v___x_1781_; 
lean_dec_ref_known(v_ctx_1780_, 1);
v___x_1781_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__1));
return v___x_1781_;
}
case 1:
{
lean_object* v_parentDecl_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1795_; 
v_parentDecl_1782_ = lean_ctor_get(v_ctx_1780_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_ctx_1780_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1784_ = v_ctx_1780_;
v_isShared_1785_ = v_isSharedCheck_1795_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_parentDecl_1782_);
lean_dec(v_ctx_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1795_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1786_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__2));
v___x_1787_ = 1;
v___x_1788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_parentDecl_1782_, v___x_1787_);
v___x_1789_ = lean_string_append(v___x_1786_, v___x_1788_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 3);
lean_ctor_set(v___x_1784_, 0, v___x_1791_);
v___x_1793_ = v___x_1784_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
default: 
{
lean_object* v_autoImplicits_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1811_; 
v_autoImplicits_1796_ = lean_ctor_get(v_ctx_1780_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_ctx_1780_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1798_ = v_ctx_1780_;
v_isShared_1799_ = v_isSharedCheck_1811_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_autoImplicits_1796_);
lean_dec(v_ctx_1780_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1811_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1800_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__3));
v___x_1801_ = ((lean_object*)(l_Lean_Elab_PartialContextInfo_format___closed__4));
v___x_1802_ = lean_array_to_list(v_autoImplicits_1796_);
v___x_1803_ = l_List_toString___at___00Lean_Elab_PartialContextInfo_format_spec__0(v___x_1802_);
lean_dec(v___x_1802_);
v___x_1804_ = lean_string_append(v___x_1801_, v___x_1803_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = lean_string_append(v___x_1800_, v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = ((lean_object*)(l_Lean_Elab_DelabTermInfo_docString_x3f___closed__1));
v___x_1807_ = lean_string_append(v___x_1805_, v___x_1806_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 3);
lean_ctor_set(v___x_1798_, 0, v___x_1807_);
v___x_1809_ = v___x_1798_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format(lean_object* v_tree_1821_, lean_object* v_ctx_x3f_1822_){
_start:
{
switch(lean_obj_tag(v_tree_1821_))
{
case 0:
{
lean_object* v_i_1824_; lean_object* v_t_1825_; lean_object* v___x_1826_; 
v_i_1824_ = lean_ctor_get(v_tree_1821_, 0);
lean_inc_ref(v_i_1824_);
v_t_1825_ = lean_ctor_get(v_tree_1821_, 1);
lean_inc_ref(v_t_1825_);
lean_dec_ref_known(v_tree_1821_, 2);
v___x_1826_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1824_, v_ctx_x3f_1822_);
v_tree_1821_ = v_t_1825_;
v_ctx_x3f_1822_ = v___x_1826_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_ctx_x3f_1822_) == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref_known(v_tree_1821_, 2);
v___x_1828_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__1));
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
else
{
lean_object* v_i_1830_; lean_object* v_children_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1881_; 
v_i_1830_ = lean_ctor_get(v_tree_1821_, 0);
v_children_1831_ = lean_ctor_get(v_tree_1821_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_tree_1821_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1833_ = v_tree_1821_;
v_isShared_1834_ = v_isSharedCheck_1881_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_children_1831_);
lean_inc(v_i_1830_);
lean_dec(v_tree_1821_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1881_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_val_1835_; lean_object* v___x_1836_; 
v_val_1835_ = lean_ctor_get(v_ctx_x3f_1822_, 0);
lean_inc_ref(v_i_1830_);
lean_inc(v_val_1835_);
v___x_1836_ = l_Lean_Elab_Info_format(v_val_1835_, v_i_1830_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1880_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1880_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1880_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_size_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_size_1841_ = lean_ctor_get(v_children_1831_, 2);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_nat_dec_eq(v_size_1841_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_del_object(v___x_1839_);
v___x_1844_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_1822_, v_i_1830_);
lean_dec_ref(v_i_1830_);
v___x_1845_ = l_Lean_PersistentArray_toList___redArg(v_children_1831_);
lean_dec_ref(v_children_1831_);
v___x_1846_ = lean_box(0);
v___x_1847_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1844_, v___x_1845_, v___x_1846_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1863_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1863_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1863_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1834_ == 0)
{
lean_ctor_set_tag(v___x_1833_, 5);
lean_ctor_set(v___x_1833_, 1, v_a_1837_);
lean_ctor_set(v___x_1833_, 0, v___x_1852_);
v___x_1854_ = v___x_1833_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_a_1837_);
v___x_1854_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1855_ = lean_box(1);
v___x_1856_ = l_Std_Format_prefixJoin___at___00Lean_Elab_ContextInfo_ppGoals_spec__1(v___x_1855_, v_a_1848_);
v___x_1857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1854_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = l_Std_Format_nestD(v___x_1857_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1858_);
v___x_1860_ = v___x_1850_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_a_1837_);
lean_del_object(v___x_1833_);
v_a_1864_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1847_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1847_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec_ref(v_children_1831_);
lean_dec_ref(v_i_1830_);
lean_dec_ref_known(v_ctx_x3f_1822_, 1);
v___x_1872_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__3));
if (v_isShared_1834_ == 0)
{
lean_ctor_set_tag(v___x_1833_, 5);
lean_ctor_set(v___x_1833_, 1, v_a_1837_);
lean_ctor_set(v___x_1833_, 0, v___x_1872_);
v___x_1874_ = v___x_1833_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_a_1837_);
v___x_1874_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1875_ = l_Std_Format_nestD(v___x_1874_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1875_);
v___x_1877_ = v___x_1839_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
else
{
lean_del_object(v___x_1833_);
lean_dec_ref(v_children_1831_);
lean_dec_ref(v_i_1830_);
lean_dec_ref_known(v_ctx_x3f_1822_, 1);
return v___x_1836_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_ctx_x3f_1822_);
v_mvarId_1882_ = lean_ctor_get(v_tree_1821_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_tree_1821_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1884_ = v_tree_1821_;
v_isShared_1885_ = v_isSharedCheck_1895_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_mvarId_1882_);
lean_dec(v_tree_1821_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1895_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1886_ = ((lean_object*)(l_Lean_Elab_InfoTree_format___closed__5));
v___x_1887_ = 1;
v___x_1888_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1882_, v___x_1887_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 3);
lean_ctor_set(v___x_1884_, 0, v___x_1888_);
v___x_1890_ = v___x_1884_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1886_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Std_Format_nestD(v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(lean_object* v___x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
if (lean_obj_tag(v_x_1897_) == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_dec(v___x_1896_);
v___x_1900_ = l_List_reverse___redArg(v_x_1898_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
else
{
lean_object* v_head_1902_; lean_object* v_tail_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1921_; 
v_head_1902_ = lean_ctor_get(v_x_1897_, 0);
v_tail_1903_ = lean_ctor_get(v_x_1897_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_x_1897_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1905_ = v_x_1897_;
v_isShared_1906_ = v_isSharedCheck_1921_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_tail_1903_);
lean_inc(v_head_1902_);
lean_dec(v_x_1897_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1921_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; 
lean_inc(v___x_1896_);
v___x_1907_ = l_Lean_Elab_InfoTree_format(v_head_1902_, v___x_1896_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 1, v_x_1898_);
lean_ctor_set(v___x_1905_, 0, v_a_1908_);
v___x_1910_ = v___x_1905_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1908_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_x_1898_);
v___x_1910_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
v_x_1897_ = v_tail_1903_;
v_x_1898_ = v___x_1910_;
goto _start;
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_del_object(v___x_1905_);
lean_dec(v_tail_1903_);
lean_dec(v_x_1898_);
lean_dec(v___x_1896_);
v_a_1913_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1907_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1907_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0___boxed(lean_object* v___x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_List_mapM_loop___at___00Lean_Elab_InfoTree_format_spec__0(v___x_1922_, v_x_1923_, v_x_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_format___boxed(lean_object* v_tree_1927_, lean_object* v_ctx_x3f_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Elab_InfoTree_format(v_tree_1927_, v_ctx_x3f_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0(lean_object* v_f_1931_, lean_object* v_s_1932_){
_start:
{
uint8_t v_enabled_1933_; lean_object* v_assignment_1934_; lean_object* v_lazyAssignment_1935_; lean_object* v_trees_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_enabled_1933_ = lean_ctor_get_uint8(v_s_1932_, sizeof(void*)*3);
v_assignment_1934_ = lean_ctor_get(v_s_1932_, 0);
v_lazyAssignment_1935_ = lean_ctor_get(v_s_1932_, 1);
v_trees_1936_ = lean_ctor_get(v_s_1932_, 2);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_s_1932_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1938_ = v_s_1932_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_trees_1936_);
lean_inc(v_lazyAssignment_1935_);
lean_inc(v_assignment_1934_);
lean_dec(v_s_1932_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_apply_1(v_f_1931_, v_trees_1936_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 2, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_assignment_1934_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_lazyAssignment_1935_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v___x_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1943_, sizeof(void*)*3, v_enabled_1933_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg(lean_object* v_inst_1945_, lean_object* v_f_1946_){
_start:
{
lean_object* v_modifyInfoState_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; 
v_modifyInfoState_1947_ = lean_ctor_get(v_inst_1945_, 1);
lean_inc(v_modifyInfoState_1947_);
lean_dec_ref(v_inst_1945_);
v___f_1948_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1948_, 0, v_f_1946_);
v___x_1949_ = lean_apply_1(v_modifyInfoState_1947_, v___f_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees(lean_object* v_m_1950_, lean_object* v_inst_1951_, lean_object* v_f_1952_){
_start:
{
lean_object* v_modifyInfoState_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; 
v_modifyInfoState_1953_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc(v_modifyInfoState_1953_);
lean_dec_ref(v_inst_1951_);
v___f_1954_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_modifyInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1954_, 0, v_f_1952_);
v___x_1955_ = lean_apply_1(v_modifyInfoState_1953_, v___f_1954_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_unsigned_to_nat(32u);
v___x_1957_ = lean_mk_empty_array_with_capacity(v___x_1956_);
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1959_ = ((size_t)5ULL);
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_unsigned_to_nat(32u);
v___x_1962_ = lean_mk_empty_array_with_capacity(v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__0);
v___x_1964_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v___x_1962_);
lean_ctor_set(v___x_1964_, 2, v___x_1960_);
lean_ctor_set(v___x_1964_, 3, v___x_1960_);
lean_ctor_set_usize(v___x_1964_, 4, v___x_1959_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__0(lean_object* v_s_1965_){
_start:
{
uint8_t v_enabled_1966_; lean_object* v_assignment_1967_; lean_object* v_lazyAssignment_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
v_enabled_1966_ = lean_ctor_get_uint8(v_s_1965_, sizeof(void*)*3);
v_assignment_1967_ = lean_ctor_get(v_s_1965_, 0);
v_lazyAssignment_1968_ = lean_ctor_get(v_s_1965_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_s_1965_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_s_1965_, 2);
lean_dec(v_unused_1977_);
v___x_1970_ = v_s_1965_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_lazyAssignment_1968_);
lean_inc(v_assignment_1967_);
lean_dec(v_s_1965_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 2, v___x_1972_);
v___x_1974_ = v___x_1970_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_assignment_1967_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_lazyAssignment_1968_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v___x_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3, v_enabled_1966_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__1(lean_object* v_toPure_1978_, lean_object* v_trees_1979_, lean_object* v_____r_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_apply_2(v_toPure_1978_, lean_box(0), v_trees_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg___lam__2(lean_object* v_toPure_1982_, lean_object* v_modifyInfoState_1983_, lean_object* v___f_1984_, lean_object* v_toBind_1985_, lean_object* v_____do__lift_1986_){
_start:
{
lean_object* v_trees_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_trees_1987_ = lean_ctor_get(v_____do__lift_1986_, 2);
lean_inc_ref(v_trees_1987_);
lean_dec_ref(v_____do__lift_1986_);
v___f_1988_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1988_, 0, v_toPure_1982_);
lean_closure_set(v___f_1988_, 1, v_trees_1987_);
v___x_1989_ = lean_apply_1(v_modifyInfoState_1983_, v___f_1984_);
v___x_1990_ = lean_apply_4(v_toBind_1985_, lean_box(0), lean_box(0), v___x_1989_, v___f_1988_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___redArg(lean_object* v_inst_1992_, lean_object* v_inst_1993_){
_start:
{
lean_object* v_toApplicative_1994_; lean_object* v_toBind_1995_; lean_object* v_getInfoState_1996_; lean_object* v_modifyInfoState_1997_; lean_object* v_toPure_1998_; lean_object* v___f_1999_; lean_object* v___f_2000_; lean_object* v___x_2001_; 
v_toApplicative_1994_ = lean_ctor_get(v_inst_1992_, 0);
lean_inc_ref(v_toApplicative_1994_);
v_toBind_1995_ = lean_ctor_get(v_inst_1992_, 1);
lean_inc_n(v_toBind_1995_, 2);
lean_dec_ref(v_inst_1992_);
v_getInfoState_1996_ = lean_ctor_get(v_inst_1993_, 0);
lean_inc(v_getInfoState_1996_);
v_modifyInfoState_1997_ = lean_ctor_get(v_inst_1993_, 1);
lean_inc(v_modifyInfoState_1997_);
lean_dec_ref(v_inst_1993_);
v_toPure_1998_ = lean_ctor_get(v_toApplicative_1994_, 1);
lean_inc(v_toPure_1998_);
lean_dec_ref(v_toApplicative_1994_);
v___f_1999_ = ((lean_object*)(l_Lean_Elab_getResetInfoTrees___redArg___closed__0));
v___f_2000_ = lean_alloc_closure((void*)(l_Lean_Elab_getResetInfoTrees___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2000_, 0, v_toPure_1998_);
lean_closure_set(v___f_2000_, 1, v_modifyInfoState_1997_);
lean_closure_set(v___f_2000_, 2, v___f_1999_);
lean_closure_set(v___f_2000_, 3, v_toBind_1995_);
v___x_2001_ = lean_apply_4(v_toBind_1995_, lean_box(0), lean_box(0), v_getInfoState_1996_, v___f_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees(lean_object* v_m_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2003_, v_inst_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__0(lean_object* v_t_2006_, lean_object* v_s_2007_){
_start:
{
uint8_t v_enabled_2008_; lean_object* v_assignment_2009_; lean_object* v_lazyAssignment_2010_; lean_object* v_trees_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
v_enabled_2008_ = lean_ctor_get_uint8(v_s_2007_, sizeof(void*)*3);
v_assignment_2009_ = lean_ctor_get(v_s_2007_, 0);
v_lazyAssignment_2010_ = lean_ctor_get(v_s_2007_, 1);
v_trees_2011_ = lean_ctor_get(v_s_2007_, 2);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_s_2007_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2013_ = v_s_2007_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_trees_2011_);
lean_inc(v_lazyAssignment_2010_);
lean_inc(v_assignment_2009_);
lean_dec(v_s_2007_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = l_Lean_PersistentArray_push___redArg(v_trees_2011_, v_t_2006_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 2, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_assignment_2009_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_lazyAssignment_2010_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v___x_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*3, v_enabled_2008_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1(lean_object* v_toApplicative_2020_, lean_object* v_modifyInfoState_2021_, lean_object* v___f_2022_, lean_object* v_____do__lift_2023_){
_start:
{
uint8_t v_enabled_2024_; 
v_enabled_2024_ = lean_ctor_get_uint8(v_____do__lift_2023_, sizeof(void*)*3);
if (v_enabled_2024_ == 0)
{
lean_object* v_toPure_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec_ref(v___f_2022_);
lean_dec(v_modifyInfoState_2021_);
v_toPure_2025_ = lean_ctor_get(v_toApplicative_2020_, 1);
lean_inc(v_toPure_2025_);
lean_dec_ref(v_toApplicative_2020_);
v___x_2026_ = lean_box(0);
v___x_2027_ = lean_apply_2(v_toPure_2025_, lean_box(0), v___x_2026_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; 
lean_dec_ref(v_toApplicative_2020_);
v___x_2028_ = lean_apply_1(v_modifyInfoState_2021_, v___f_2022_);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed(lean_object* v_toApplicative_2029_, lean_object* v_modifyInfoState_2030_, lean_object* v___f_2031_, lean_object* v_____do__lift_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_Elab_pushInfoTree___redArg___lam__1(v_toApplicative_2029_, v_modifyInfoState_2030_, v___f_2031_, v_____do__lift_2032_);
lean_dec_ref(v_____do__lift_2032_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___redArg(lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_t_2036_){
_start:
{
lean_object* v_toApplicative_2037_; lean_object* v_toBind_2038_; lean_object* v_getInfoState_2039_; lean_object* v_modifyInfoState_2040_; lean_object* v___f_2041_; lean_object* v___f_2042_; lean_object* v___x_2043_; 
v_toApplicative_2037_ = lean_ctor_get(v_inst_2034_, 0);
lean_inc_ref(v_toApplicative_2037_);
v_toBind_2038_ = lean_ctor_get(v_inst_2034_, 1);
lean_inc(v_toBind_2038_);
lean_dec_ref(v_inst_2034_);
v_getInfoState_2039_ = lean_ctor_get(v_inst_2035_, 0);
lean_inc(v_getInfoState_2039_);
v_modifyInfoState_2040_ = lean_ctor_get(v_inst_2035_, 1);
lean_inc(v_modifyInfoState_2040_);
lean_dec_ref(v_inst_2035_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2041_, 0, v_t_2036_);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2042_, 0, v_toApplicative_2037_);
lean_closure_set(v___f_2042_, 1, v_modifyInfoState_2040_);
lean_closure_set(v___f_2042_, 2, v___f_2041_);
v___x_2043_ = lean_apply_4(v_toBind_2038_, lean_box(0), lean_box(0), v_getInfoState_2039_, v___f_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree(lean_object* v_m_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_t_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2045_, v_inst_2046_, v_t_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0(lean_object* v_toApplicative_2049_, lean_object* v_t_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_____do__lift_2053_){
_start:
{
uint8_t v_enabled_2054_; 
v_enabled_2054_ = lean_ctor_get_uint8(v_____do__lift_2053_, sizeof(void*)*3);
if (v_enabled_2054_ == 0)
{
lean_object* v_toPure_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v_inst_2052_);
lean_dec_ref(v_inst_2051_);
lean_dec_ref(v_t_2050_);
v_toPure_2055_ = lean_ctor_get(v_toApplicative_2049_, 1);
lean_inc(v_toPure_2055_);
lean_dec_ref(v_toApplicative_2049_);
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_apply_2(v_toPure_2055_, lean_box(0), v___x_2056_);
return v___x_2057_;
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec_ref(v_toApplicative_2049_);
v___x_2058_ = lean_unsigned_to_nat(32u);
v___x_2059_ = lean_mk_empty_array_with_capacity(v___x_2058_);
lean_dec_ref(v___x_2059_);
v___x_2060_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2061_, 0, v_t_2050_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = l_Lean_Elab_pushInfoTree___redArg(v_inst_2051_, v_inst_2052_, v___x_2061_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed(lean_object* v_toApplicative_2063_, lean_object* v_t_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_____do__lift_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Elab_pushInfoLeaf___redArg___lam__0(v_toApplicative_2063_, v_t_2064_, v_inst_2065_, v_inst_2066_, v_____do__lift_2067_);
lean_dec_ref(v_____do__lift_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_t_2071_){
_start:
{
lean_object* v_toApplicative_2072_; lean_object* v_toBind_2073_; lean_object* v_getInfoState_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; 
v_toApplicative_2072_ = lean_ctor_get(v_inst_2069_, 0);
lean_inc_ref(v_toApplicative_2072_);
v_toBind_2073_ = lean_ctor_get(v_inst_2069_, 1);
lean_inc(v_toBind_2073_);
v_getInfoState_2074_ = lean_ctor_get(v_inst_2070_, 0);
lean_inc(v_getInfoState_2074_);
v___f_2075_ = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoLeaf___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2075_, 0, v_toApplicative_2072_);
lean_closure_set(v___f_2075_, 1, v_t_2071_);
lean_closure_set(v___f_2075_, 2, v_inst_2069_);
lean_closure_set(v___f_2075_, 3, v_inst_2070_);
v___x_2076_ = lean_apply_4(v_toBind_2073_, lean_box(0), lean_box(0), v_getInfoState_2074_, v___f_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf(lean_object* v_m_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_t_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2078_, v_inst_2079_, v_t_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_info_2084_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_info_2084_);
v___x_2086_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2082_, v_inst_2083_, v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo(lean_object* v_m_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_info_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Elab_addCompletionInfo___redArg(v_inst_2088_, v_inst_2089_, v_info_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg___lam__0(lean_object* v_stx_2092_, lean_object* v_expectedType_x3f_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_____do__lift_2096_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_stx_2092_);
v___x_2099_ = l_Lean_LocalContext_empty;
v___x_2100_ = 0;
v___x_2101_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2101_, 0, v___x_2098_);
lean_ctor_set(v___x_2101_, 1, v___x_2099_);
lean_ctor_set(v___x_2101_, 2, v_expectedType_x3f_2093_);
lean_ctor_set(v___x_2101_, 3, v_____do__lift_2096_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*4, v___x_2100_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*4 + 1, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
v___x_2103_ = l_Lean_Elab_pushInfoLeaf___redArg(v_inst_2094_, v_inst_2095_, v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_stx_2108_, lean_object* v_n_2109_, lean_object* v_expectedType_x3f_2110_){
_start:
{
lean_object* v_toBind_2111_; lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_toBind_2111_ = lean_ctor_get(v_inst_2104_, 1);
lean_inc(v_toBind_2111_);
lean_inc_ref(v_inst_2104_);
v___f_2112_ = lean_alloc_closure((void*)(l_Lean_Elab_addConstInfo___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2112_, 0, v_stx_2108_);
lean_closure_set(v___f_2112_, 1, v_expectedType_x3f_2110_);
lean_closure_set(v___f_2112_, 2, v_inst_2104_);
lean_closure_set(v___f_2112_, 3, v_inst_2105_);
v___x_2113_ = l_Lean_mkConstWithLevelParams___redArg(v_inst_2104_, v_inst_2106_, v_inst_2107_, v_n_2109_);
v___x_2114_ = lean_apply_4(v_toBind_2111_, lean_box(0), lean_box(0), v___x_2113_, v___f_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo(lean_object* v_m_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_stx_2120_, lean_object* v_n_2121_, lean_object* v_expectedType_x3f_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Elab_addConstInfo___redArg(v_inst_2116_, v_inst_2117_, v_inst_2118_, v_inst_2119_, v_stx_2120_, v_n_2121_, v_expectedType_x3f_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(lean_object* v_t_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v_infoState_2128_; uint8_t v_enabled_2129_; 
v___x_2127_ = lean_st_ref_get(v___y_2125_);
v_infoState_2128_ = lean_ctor_get(v___x_2127_, 7);
lean_inc_ref(v_infoState_2128_);
lean_dec(v___x_2127_);
v_enabled_2129_ = lean_ctor_get_uint8(v_infoState_2128_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2128_);
if (v_enabled_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec_ref(v_t_2124_);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; lean_object* v_infoState_2133_; lean_object* v_env_2134_; lean_object* v_nextMacroScope_2135_; lean_object* v_ngen_2136_; lean_object* v_auxDeclNGen_2137_; lean_object* v_traceState_2138_; lean_object* v_cache_2139_; lean_object* v_messages_2140_; lean_object* v_snapshotTasks_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2163_; 
v___x_2132_ = lean_st_ref_take(v___y_2125_);
v_infoState_2133_ = lean_ctor_get(v___x_2132_, 7);
v_env_2134_ = lean_ctor_get(v___x_2132_, 0);
v_nextMacroScope_2135_ = lean_ctor_get(v___x_2132_, 1);
v_ngen_2136_ = lean_ctor_get(v___x_2132_, 2);
v_auxDeclNGen_2137_ = lean_ctor_get(v___x_2132_, 3);
v_traceState_2138_ = lean_ctor_get(v___x_2132_, 4);
v_cache_2139_ = lean_ctor_get(v___x_2132_, 5);
v_messages_2140_ = lean_ctor_get(v___x_2132_, 6);
v_snapshotTasks_2141_ = lean_ctor_get(v___x_2132_, 8);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2143_ = v___x_2132_;
v_isShared_2144_ = v_isSharedCheck_2163_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_snapshotTasks_2141_);
lean_inc(v_infoState_2133_);
lean_inc(v_messages_2140_);
lean_inc(v_cache_2139_);
lean_inc(v_traceState_2138_);
lean_inc(v_auxDeclNGen_2137_);
lean_inc(v_ngen_2136_);
lean_inc(v_nextMacroScope_2135_);
lean_inc(v_env_2134_);
lean_dec(v___x_2132_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2163_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
uint8_t v_enabled_2145_; lean_object* v_assignment_2146_; lean_object* v_lazyAssignment_2147_; lean_object* v_trees_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2162_; 
v_enabled_2145_ = lean_ctor_get_uint8(v_infoState_2133_, sizeof(void*)*3);
v_assignment_2146_ = lean_ctor_get(v_infoState_2133_, 0);
v_lazyAssignment_2147_ = lean_ctor_get(v_infoState_2133_, 1);
v_trees_2148_ = lean_ctor_get(v_infoState_2133_, 2);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_infoState_2133_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2150_ = v_infoState_2133_;
v_isShared_2151_ = v_isSharedCheck_2162_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_trees_2148_);
lean_inc(v_lazyAssignment_2147_);
lean_inc(v_assignment_2146_);
lean_dec(v_infoState_2133_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2162_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = l_Lean_PersistentArray_push___redArg(v_trees_2148_, v_t_2124_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 2, v___x_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_assignment_2146_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_lazyAssignment_2147_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v___x_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*3, v_enabled_2145_);
v___x_2154_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2156_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 7, v___x_2154_);
v___x_2156_ = v___x_2143_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_env_2134_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_nextMacroScope_2135_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_ngen_2136_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_auxDeclNGen_2137_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_traceState_2138_);
lean_ctor_set(v_reuseFailAlloc_2160_, 5, v_cache_2139_);
lean_ctor_set(v_reuseFailAlloc_2160_, 6, v_messages_2140_);
lean_ctor_set(v_reuseFailAlloc_2160_, 7, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2160_, 8, v_snapshotTasks_2141_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_st_ref_put(v___y_2125_, v___x_2156_);
v___x_2158_ = lean_box(0);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_t_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2164_, v___y_2165_);
lean_dec(v___y_2165_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(lean_object* v_t_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; lean_object* v_infoState_2173_; uint8_t v_enabled_2174_; 
v___x_2172_ = lean_st_ref_get(v___y_2170_);
v_infoState_2173_ = lean_ctor_get(v___x_2172_, 7);
lean_inc_ref(v_infoState_2173_);
lean_dec(v___x_2172_);
v_enabled_2174_ = lean_ctor_get_uint8(v_infoState_2173_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2173_);
if (v_enabled_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v_t_2168_);
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
return v___x_2176_;
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2177_ = lean_unsigned_to_nat(32u);
v___x_2178_ = lean_mk_empty_array_with_capacity(v___x_2177_);
lean_dec_ref(v___x_2178_);
v___x_2179_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1, &l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___redArg___lam__0___closed__1);
v___x_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2180_, 0, v_t_2168_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v___x_2180_, v___y_2170_);
return v___x_2181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1___boxed(lean_object* v_t_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v_t_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
lean_ctor_set(v___x_2192_, 2, v___x_2191_);
lean_ctor_set(v___x_2192_, 3, v___x_2191_);
lean_ctor_set(v___x_2192_, 4, v___x_2190_);
lean_ctor_set(v___x_2192_, 5, v___x_2190_);
lean_ctor_set(v___x_2192_, 6, v___x_2190_);
lean_ctor_set(v___x_2192_, 7, v___x_2190_);
lean_ctor_set(v___x_2192_, 8, v___x_2190_);
lean_ctor_set(v___x_2192_, 9, v___x_2190_);
lean_ctor_set(v___x_2192_, 10, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = lean_box(1);
v___x_2194_ = lean_obj_once(&l_Lean_Elab_ContextInfo_ppGoals___closed__3, &l_Lean_Elab_ContextInfo_ppGoals___closed__3_once, _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3);
v___x_2195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_2196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2194_);
lean_ctor_set(v___x_2196_, 2, v___x_2193_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__4));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_2205_ = l_Lean_stringToMessageData(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_2211_ = l_Lean_stringToMessageData(v___x_2210_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_2214_ = l_Lean_stringToMessageData(v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_2217_ = l_Lean_stringToMessageData(v___x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_2218_, lean_object* v_declHint_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v_env_2223_; uint8_t v___x_2224_; 
v___x_2222_ = lean_st_ref_get(v___y_2220_);
v_env_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc_ref(v_env_2223_);
lean_dec(v___x_2222_);
v___x_2224_ = l_Lean_Name_isAnonymous(v_declHint_2219_);
if (v___x_2224_ == 0)
{
uint8_t v_isExporting_2225_; 
v_isExporting_2225_ = lean_ctor_get_uint8(v_env_2223_, sizeof(void*)*8);
if (v_isExporting_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec_ref(v_env_2223_);
lean_dec(v_declHint_2219_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_msg_2218_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
lean_inc_ref(v_env_2223_);
v___x_2227_ = l_Lean_Environment_setExporting(v_env_2223_, v___x_2224_);
lean_inc(v_declHint_2219_);
lean_inc_ref(v___x_2227_);
v___x_2228_ = l_Lean_Environment_contains(v___x_2227_, v_declHint_2219_, v_isExporting_2225_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref(v___x_2227_);
lean_dec_ref(v_env_2223_);
lean_dec(v_declHint_2219_);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_msg_2218_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_c_2235_; lean_object* v___x_2236_; 
v___x_2230_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2231_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_2232_ = l_Lean_Options_empty;
v___x_2233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2227_);
lean_ctor_set(v___x_2233_, 1, v___x_2230_);
lean_ctor_set(v___x_2233_, 2, v___x_2231_);
lean_ctor_set(v___x_2233_, 3, v___x_2232_);
lean_inc(v_declHint_2219_);
v___x_2234_ = l_Lean_MessageData_ofConstName(v_declHint_2219_, v___x_2224_);
v_c_2235_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2235_, 0, v___x_2233_);
lean_ctor_set(v_c_2235_, 1, v___x_2234_);
v___x_2236_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2223_, v_declHint_2219_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec_ref(v_env_2223_);
lean_dec(v_declHint_2219_);
v___x_2237_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v_c_2235_);
v___x_2239_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_2240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = l_Lean_MessageData_note(v___x_2240_);
v___x_2242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_msg_2218_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
else
{
lean_object* v_val_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2279_; 
v_val_2244_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2246_ = v___x_2236_;
v_isShared_2247_ = v_isSharedCheck_2279_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_val_2244_);
lean_dec(v___x_2236_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2279_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v_mod_2251_; uint8_t v___x_2252_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = l_Lean_Environment_header(v_env_2223_);
lean_dec_ref(v_env_2223_);
v___x_2250_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2249_);
v_mod_2251_ = lean_array_get(v___x_2248_, v___x_2250_, v_val_2244_);
lean_dec(v_val_2244_);
lean_dec_ref(v___x_2250_);
v___x_2252_ = l_Lean_isPrivateName(v_declHint_2219_);
lean_dec(v_declHint_2219_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v_c_2235_);
v___x_2255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_MessageData_ofName(v_mod_2251_);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = l_Lean_MessageData_note(v___x_2260_);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_msg_2218_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set_tag(v___x_2246_, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2262_);
v___x_2264_ = v___x_2246_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v_c_2235_);
v___x_2268_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = l_Lean_MessageData_ofName(v_mod_2251_);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = l_Lean_MessageData_note(v___x_2273_);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v_msg_2218_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set_tag(v___x_2246_, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2275_);
v___x_2277_ = v___x_2246_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2280_; 
lean_dec_ref(v_env_2223_);
lean_dec(v_declHint_2219_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_msg_2218_);
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_2281_, lean_object* v_declHint_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2281_, v_declHint_2282_, v___y_2283_);
lean_dec(v___y_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(lean_object* v_msg_2286_, lean_object* v_declHint_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2301_; 
v___x_2291_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2286_, v_declHint_2287_, v___y_2289_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2301_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2301_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2296_ = l_Lean_unknownIdentifierMessageTag;
v___x_2297_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v_a_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2297_);
v___x_2299_ = v___x_2294_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_2302_, lean_object* v_declHint_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2302_, v_declHint_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(lean_object* v_msgData_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v_env_2313_; lean_object* v_options_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2312_ = lean_st_ref_get(v___y_2310_);
v_env_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc_ref(v_env_2313_);
lean_dec(v___x_2312_);
v_options_2314_ = lean_ctor_get(v___y_2309_, 2);
v___x_2315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_2316_ = lean_unsigned_to_nat(32u);
v___x_2317_ = lean_mk_empty_array_with_capacity(v___x_2316_);
lean_dec_ref(v___x_2317_);
v___x_2318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
lean_inc_ref(v_options_2314_);
v___x_2319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2319_, 0, v_env_2313_);
lean_ctor_set(v___x_2319_, 1, v___x_2315_);
lean_ctor_set(v___x_2319_, 2, v___x_2318_);
lean_ctor_set(v___x_2319_, 3, v_options_2314_);
v___x_2320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v_msgData_2308_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12___boxed(lean_object* v_msgData_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msgData_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_ref_2331_; lean_object* v___x_2332_; lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2341_; 
v_ref_2331_ = lean_ctor_get(v___y_2328_, 5);
v___x_2332_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11_spec__12(v_msg_2327_, v___y_2328_, v___y_2329_);
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2341_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2341_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2339_; 
lean_inc(v_ref_2331_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v_ref_2331_);
lean_ctor_set(v___x_2337_, 1, v_a_2333_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 1);
lean_ctor_set(v___x_2335_, 0, v___x_2337_);
v___x_2339_ = v___x_2335_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msg_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_2347_, lean_object* v_msg_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_fileName_2352_; lean_object* v_fileMap_2353_; lean_object* v_options_2354_; lean_object* v_currRecDepth_2355_; lean_object* v_maxRecDepth_2356_; lean_object* v_ref_2357_; lean_object* v_currNamespace_2358_; lean_object* v_openDecls_2359_; lean_object* v_initHeartbeats_2360_; lean_object* v_maxHeartbeats_2361_; lean_object* v_quotContext_2362_; lean_object* v_currMacroScope_2363_; uint8_t v_diag_2364_; lean_object* v_cancelTk_x3f_2365_; uint8_t v_suppressElabErrors_2366_; lean_object* v_inheritedTraceOptions_2367_; lean_object* v_ref_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_fileName_2352_ = lean_ctor_get(v___y_2349_, 0);
v_fileMap_2353_ = lean_ctor_get(v___y_2349_, 1);
v_options_2354_ = lean_ctor_get(v___y_2349_, 2);
v_currRecDepth_2355_ = lean_ctor_get(v___y_2349_, 3);
v_maxRecDepth_2356_ = lean_ctor_get(v___y_2349_, 4);
v_ref_2357_ = lean_ctor_get(v___y_2349_, 5);
v_currNamespace_2358_ = lean_ctor_get(v___y_2349_, 6);
v_openDecls_2359_ = lean_ctor_get(v___y_2349_, 7);
v_initHeartbeats_2360_ = lean_ctor_get(v___y_2349_, 8);
v_maxHeartbeats_2361_ = lean_ctor_get(v___y_2349_, 9);
v_quotContext_2362_ = lean_ctor_get(v___y_2349_, 10);
v_currMacroScope_2363_ = lean_ctor_get(v___y_2349_, 11);
v_diag_2364_ = lean_ctor_get_uint8(v___y_2349_, sizeof(void*)*14);
v_cancelTk_x3f_2365_ = lean_ctor_get(v___y_2349_, 12);
v_suppressElabErrors_2366_ = lean_ctor_get_uint8(v___y_2349_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2367_ = lean_ctor_get(v___y_2349_, 13);
v_ref_2368_ = l_Lean_replaceRef(v_ref_2347_, v_ref_2357_);
lean_inc_ref(v_inheritedTraceOptions_2367_);
lean_inc(v_cancelTk_x3f_2365_);
lean_inc(v_currMacroScope_2363_);
lean_inc(v_quotContext_2362_);
lean_inc(v_maxHeartbeats_2361_);
lean_inc(v_initHeartbeats_2360_);
lean_inc(v_openDecls_2359_);
lean_inc(v_currNamespace_2358_);
lean_inc(v_maxRecDepth_2356_);
lean_inc(v_currRecDepth_2355_);
lean_inc_ref(v_options_2354_);
lean_inc_ref(v_fileMap_2353_);
lean_inc_ref(v_fileName_2352_);
v___x_2369_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2369_, 0, v_fileName_2352_);
lean_ctor_set(v___x_2369_, 1, v_fileMap_2353_);
lean_ctor_set(v___x_2369_, 2, v_options_2354_);
lean_ctor_set(v___x_2369_, 3, v_currRecDepth_2355_);
lean_ctor_set(v___x_2369_, 4, v_maxRecDepth_2356_);
lean_ctor_set(v___x_2369_, 5, v_ref_2368_);
lean_ctor_set(v___x_2369_, 6, v_currNamespace_2358_);
lean_ctor_set(v___x_2369_, 7, v_openDecls_2359_);
lean_ctor_set(v___x_2369_, 8, v_initHeartbeats_2360_);
lean_ctor_set(v___x_2369_, 9, v_maxHeartbeats_2361_);
lean_ctor_set(v___x_2369_, 10, v_quotContext_2362_);
lean_ctor_set(v___x_2369_, 11, v_currMacroScope_2363_);
lean_ctor_set(v___x_2369_, 12, v_cancelTk_x3f_2365_);
lean_ctor_set(v___x_2369_, 13, v_inheritedTraceOptions_2367_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*14, v_diag_2364_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*14 + 1, v_suppressElabErrors_2366_);
v___x_2370_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2348_, v___x_2369_, v___y_2350_);
lean_dec_ref_known(v___x_2369_, 14);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_2371_, lean_object* v_msg_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2371_, v_msg_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v_ref_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_ref_2377_, lean_object* v_msg_2378_, lean_object* v_declHint_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v_a_2384_; lean_object* v___x_2385_; 
v___x_2383_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8(v_msg_2378_, v_declHint_2379_, v___y_2380_, v___y_2381_);
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2377_, v_a_2384_, v___y_2380_, v___y_2381_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2386_, lean_object* v_msg_2387_, lean_object* v_declHint_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2386_, v_msg_2387_, v_declHint_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_ref_2386_);
return v_res_2392_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__0));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__2));
v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_2399_, lean_object* v_constName_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2404_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_2405_ = 0;
lean_inc(v_constName_2400_);
v___x_2406_ = l_Lean_MessageData_ofConstName(v_constName_2400_, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2404_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2399_, v___x_2409_, v_constName_2400_, v___y_2401_, v___y_2402_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2411_, lean_object* v_constName_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2411_, v_constName_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v_ref_2411_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_constName_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_ref_2421_; lean_object* v___x_2422_; 
v_ref_2421_ = lean_ctor_get(v___y_2418_, 5);
v___x_2422_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2421_, v_constName_2417_, v___y_2418_, v___y_2419_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_constName_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object* v_constName_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; lean_object* v_env_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; 
v___x_2432_ = lean_st_ref_get(v___y_2430_);
v_env_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc_ref(v_env_2433_);
lean_dec(v___x_2432_);
v___x_2434_ = 0;
lean_inc(v_constName_2428_);
v___x_2435_ = l_Lean_Environment_findConstVal_x3f(v_env_2433_, v_constName_2428_, v___x_2434_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2428_, v___y_2429_, v___y_2430_);
return v___x_2436_;
}
else
{
lean_object* v_val_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_constName_2428_);
v_val_2437_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_val_2437_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set_tag(v___x_2439_, 0);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_val_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_constName_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
if (lean_obj_tag(v_a_2450_) == 0)
{
lean_object* v___x_2452_; 
v___x_2452_ = l_List_reverse___redArg(v_a_2451_);
return v___x_2452_;
}
else
{
lean_object* v_head_2453_; lean_object* v_tail_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2463_; 
v_head_2453_ = lean_ctor_get(v_a_2450_, 0);
v_tail_2454_ = lean_ctor_get(v_a_2450_, 1);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_a_2450_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2456_ = v_a_2450_;
v_isShared_2457_ = v_isSharedCheck_2463_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_tail_2454_);
lean_inc(v_head_2453_);
lean_dec(v_a_2450_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2463_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2458_ = l_Lean_mkLevelParam(v_head_2453_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 1, v_a_2451_);
lean_ctor_set(v___x_2456_, 0, v___x_2458_);
v___x_2460_ = v___x_2456_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_a_2451_);
v___x_2460_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
v_a_2450_ = v_tail_2454_;
v_a_2451_ = v___x_2460_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object* v_constName_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
lean_inc(v_constName_2464_);
v___x_2468_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(v_constName_2464_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2480_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_levelParams_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v_levelParams_2473_ = lean_ctor_get(v_a_2469_, 1);
lean_inc(v_levelParams_2473_);
lean_dec(v_a_2469_);
v___x_2474_ = lean_box(0);
v___x_2475_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__2(v_levelParams_2473_, v___x_2474_);
v___x_2476_ = l_Lean_mkConst(v_constName_2464_, v___x_2475_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2476_);
v___x_2478_ = v___x_2471_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_constName_2464_);
v_a_2481_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2468_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2468_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0___boxed(lean_object* v_constName_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_constName_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object* v_stx_2494_, lean_object* v_n_2495_, lean_object* v_expectedType_x3f_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(v_n_2495_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v_stx_2494_);
v___x_2504_ = l_Lean_LocalContext_empty;
v___x_2505_ = 0;
v___x_2506_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2506_, 0, v___x_2503_);
lean_ctor_set(v___x_2506_, 1, v___x_2504_);
lean_ctor_set(v___x_2506_, 2, v_expectedType_x3f_2496_);
lean_ctor_set(v___x_2506_, 3, v_a_2501_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*4, v___x_2505_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*4 + 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
v___x_2508_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1(v___x_2507_, v___y_2497_, v___y_2498_);
return v___x_2508_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_expectedType_x3f_2496_);
lean_dec(v_stx_2494_);
v_a_2509_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2500_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2500_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0___boxed(lean_object* v_stx_2517_, lean_object* v_n_2518_, lean_object* v_expectedType_x3f_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_stx_2517_, v_n_2518_, v_expectedType_x3f_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object* v_id_2524_, lean_object* v_expectedType_x3f_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; 
lean_inc(v_id_2524_);
v___x_2529_ = l_Lean_realizeGlobalConstNoOverload(v_id_2524_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2557_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2557_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2557_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v_infoState_2535_; uint8_t v_enabled_2536_; 
v___x_2534_ = lean_st_ref_get(v_a_2527_);
v_infoState_2535_ = lean_ctor_get(v___x_2534_, 7);
lean_inc_ref(v_infoState_2535_);
lean_dec(v___x_2534_);
v_enabled_2536_ = lean_ctor_get_uint8(v_infoState_2535_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2535_);
if (v_enabled_2536_ == 0)
{
lean_object* v___x_2538_; 
lean_dec(v_expectedType_x3f_2525_);
lean_dec(v_id_2524_);
if (v_isShared_2533_ == 0)
{
v___x_2538_ = v___x_2532_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2530_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
else
{
lean_object* v___x_2540_; 
lean_del_object(v___x_2532_);
lean_inc(v_a_2530_);
v___x_2540_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2524_, v_a_2530_, v_expectedType_x3f_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v___x_2540_, 0);
lean_dec(v_unused_2548_);
v___x_2542_ = v___x_2540_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_dec(v___x_2540_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_a_2530_);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2530_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_a_2530_);
v_a_2549_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2540_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2540_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2525_);
lean_dec(v_id_2524_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object* v_id_2558_, lean_object* v_expectedType_x3f_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_2558_, v_expectedType_x3f_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(lean_object* v_t_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___redArg(v_t_2564_, v___y_2566_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4___boxed(lean_object* v_t_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__1_spec__4(v_t_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2574_, lean_object* v_constName_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___redArg(v_constName_2575_, v___y_2576_, v___y_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2580_, lean_object* v_constName_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2580_, v_constName_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2586_, lean_object* v_ref_2587_, lean_object* v_constName_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___redArg(v_ref_2587_, v_constName_2588_, v___y_2589_, v___y_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2593_, lean_object* v_ref_2594_, lean_object* v_constName_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5(v_00_u03b1_2593_, v_ref_2594_, v_constName_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v_ref_2594_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_2600_, lean_object* v_ref_2601_, lean_object* v_msg_2602_, lean_object* v_declHint_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___redArg(v_ref_2601_, v_msg_2602_, v_declHint_2603_, v___y_2604_, v___y_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2608_, lean_object* v_ref_2609_, lean_object* v_msg_2610_, lean_object* v_declHint_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_2608_, v_ref_2609_, v_msg_2610_, v_declHint_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v_ref_2609_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_2616_, lean_object* v_declHint_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2616_, v_declHint_2617_, v___y_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_2622_, lean_object* v_declHint_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__8_spec__9(v_msg_2622_, v_declHint_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2628_, lean_object* v_ref_2629_, lean_object* v_msg_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___redArg(v_ref_2629_, v_msg_2630_, v___y_2631_, v___y_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2635_, lean_object* v_ref_2636_, lean_object* v_msg_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9(v_00_u03b1_2635_, v_ref_2636_, v_msg_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v_ref_2636_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_2642_, lean_object* v_msg_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___redArg(v_msg_2643_, v___y_2644_, v___y_2645_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_2648_, lean_object* v_msg_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1_spec__2_spec__5_spec__7_spec__9_spec__11(v_00_u03b1_2648_, v_msg_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(lean_object* v_id_2654_, lean_object* v_expectedType_x3f_2655_, lean_object* v_as_x27_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
if (lean_obj_tag(v_as_x27_2656_) == 0)
{
lean_object* v___x_2661_; 
lean_dec(v_expectedType_x3f_2655_);
lean_dec(v_id_2654_);
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v_b_2657_);
return v___x_2661_;
}
else
{
lean_object* v_head_2662_; lean_object* v_tail_2663_; lean_object* v___x_2664_; 
v_head_2662_ = lean_ctor_get(v_as_x27_2656_, 0);
v_tail_2663_ = lean_ctor_get(v_as_x27_2656_, 1);
lean_inc(v_expectedType_x3f_2655_);
lean_inc(v_head_2662_);
lean_inc(v_id_2654_);
v___x_2664_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_id_2654_, v_head_2662_, v_expectedType_x3f_2655_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v___x_2665_; 
lean_dec_ref_known(v___x_2664_, 1);
v___x_2665_ = lean_box(0);
v_as_x27_2656_ = v_tail_2663_;
v_b_2657_ = v___x_2665_;
goto _start;
}
else
{
lean_dec(v_expectedType_x3f_2655_);
lean_dec(v_id_2654_);
return v___x_2664_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg___boxed(lean_object* v_id_2667_, lean_object* v_expectedType_x3f_2668_, lean_object* v_as_x27_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2667_, v_expectedType_x3f_2668_, v_as_x27_2669_, v_b_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v_as_x27_2669_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object* v_id_2675_, lean_object* v_expectedType_x3f_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v___x_2680_; 
lean_inc(v_id_2675_);
v___x_2680_ = l_Lean_realizeGlobalConst(v_id_2675_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2709_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2709_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2709_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v_infoState_2686_; uint8_t v_enabled_2687_; 
v___x_2685_ = lean_st_ref_get(v_a_2678_);
v_infoState_2686_ = lean_ctor_get(v___x_2685_, 7);
lean_inc_ref(v_infoState_2686_);
lean_dec(v___x_2685_);
v_enabled_2687_ = lean_ctor_get_uint8(v_infoState_2686_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2686_);
if (v_enabled_2687_ == 0)
{
lean_object* v___x_2689_; 
lean_dec(v_expectedType_x3f_2676_);
lean_dec(v_id_2675_);
if (v_isShared_2684_ == 0)
{
v___x_2689_ = v___x_2683_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2681_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_del_object(v___x_2683_);
v___x_2691_ = lean_box(0);
v___x_2692_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2675_, v_expectedType_x3f_2676_, v_a_2681_, v___x_2691_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2692_, 0);
lean_dec(v_unused_2700_);
v___x_2694_ = v___x_2692_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_dec(v___x_2692_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v_a_2681_);
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2681_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_a_2681_);
v_a_2701_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2692_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2692_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
else
{
lean_dec(v_expectedType_x3f_2676_);
lean_dec(v_id_2675_);
return v___x_2680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object* v_id_2710_, lean_object* v_expectedType_x3f_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Elab_realizeGlobalConstWithInfos(v_id_2710_, v_expectedType_x3f_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(lean_object* v_id_2716_, lean_object* v_expectedType_x3f_2717_, lean_object* v_as_2718_, lean_object* v_as_x27_2719_, lean_object* v_b_2720_, lean_object* v_a_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___redArg(v_id_2716_, v_expectedType_x3f_2717_, v_as_x27_2719_, v_b_2720_, v___y_2722_, v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0___boxed(lean_object* v_id_2726_, lean_object* v_expectedType_x3f_2727_, lean_object* v_as_2728_, lean_object* v_as_x27_2729_, lean_object* v_b_2730_, lean_object* v_a_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalConstWithInfos_spec__0(v_id_2726_, v_expectedType_x3f_2727_, v_as_2728_, v_as_x27_2729_, v_b_2730_, v_a_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v_as_x27_2729_);
lean_dec(v_as_2728_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(lean_object* v_ref_2736_, lean_object* v_as_x27_2737_, lean_object* v_b_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
if (lean_obj_tag(v_as_x27_2737_) == 0)
{
lean_object* v___x_2742_; 
lean_dec(v_ref_2736_);
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_b_2738_);
return v___x_2742_;
}
else
{
lean_object* v_head_2743_; lean_object* v_tail_2744_; lean_object* v_fst_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v_head_2743_ = lean_ctor_get(v_as_x27_2737_, 0);
v_tail_2744_ = lean_ctor_get(v_as_x27_2737_, 1);
v_fst_2745_ = lean_ctor_get(v_head_2743_, 0);
v___x_2746_ = lean_box(0);
lean_inc(v_fst_2745_);
lean_inc(v_ref_2736_);
v___x_2747_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(v_ref_2736_, v_fst_2745_, v___x_2746_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v___x_2748_; 
lean_dec_ref_known(v___x_2747_, 1);
v___x_2748_ = lean_box(0);
v_as_x27_2737_ = v_tail_2744_;
v_b_2738_ = v___x_2748_;
goto _start;
}
else
{
lean_dec(v_ref_2736_);
return v___x_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg___boxed(lean_object* v_ref_2750_, lean_object* v_as_x27_2751_, lean_object* v_b_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2750_, v_as_x27_2751_, v_b_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v_as_x27_2751_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object* v_ref_2757_, lean_object* v_id_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_realizeGlobalName(v_id_2758_, v_a_2759_, v_a_2760_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2791_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2791_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2791_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v_infoState_2768_; uint8_t v_enabled_2769_; 
v___x_2767_ = lean_st_ref_get(v_a_2760_);
v_infoState_2768_ = lean_ctor_get(v___x_2767_, 7);
lean_inc_ref(v_infoState_2768_);
lean_dec(v___x_2767_);
v_enabled_2769_ = lean_ctor_get_uint8(v_infoState_2768_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2768_);
if (v_enabled_2769_ == 0)
{
lean_object* v___x_2771_; 
lean_dec(v_ref_2757_);
if (v_isShared_2766_ == 0)
{
v___x_2771_ = v___x_2765_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2763_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_del_object(v___x_2765_);
v___x_2773_ = lean_box(0);
v___x_2774_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2757_, v_a_2763_, v___x_2773_, v_a_2759_, v_a_2760_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v___x_2774_, 0);
lean_dec(v_unused_2782_);
v___x_2776_ = v___x_2774_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_dec(v___x_2774_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v_a_2763_);
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2763_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v_a_2763_);
v_a_2783_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2774_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2774_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
}
else
{
lean_dec(v_ref_2757_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_realizeGlobalNameWithInfos___boxed(lean_object* v_ref_2792_, lean_object* v_id_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Elab_realizeGlobalNameWithInfos(v_ref_2792_, v_id_2793_, v_a_2794_, v_a_2795_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(lean_object* v_ref_2798_, lean_object* v_as_2799_, lean_object* v_as_x27_2800_, lean_object* v_b_2801_, lean_object* v_a_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___redArg(v_ref_2798_, v_as_x27_2800_, v_b_2801_, v___y_2803_, v___y_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0___boxed(lean_object* v_ref_2807_, lean_object* v_as_2808_, lean_object* v_as_x27_2809_, lean_object* v_b_2810_, lean_object* v_a_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_List_forIn_x27_loop___at___00Lean_Elab_realizeGlobalNameWithInfos_spec__0(v_ref_2807_, v_as_2808_, v_as_x27_2809_, v_b_2810_, v_a_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v_as_x27_2809_);
lean_dec(v_as_2808_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0(lean_object* v_self_2816_){
_start:
{
lean_object* v_fst_2817_; 
v_fst_2817_ = lean_ctor_get(v_self_2816_, 0);
lean_inc(v_fst_2817_);
return v_fst_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__0___boxed(lean_object* v_self_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__0(v_self_2818_);
lean_dec_ref(v_self_2818_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__1(lean_object* v_info_2820_, lean_object* v_treesSaved_2821_, lean_object* v_s_2822_){
_start:
{
if (lean_obj_tag(v_info_2820_) == 0)
{
uint8_t v_enabled_2823_; lean_object* v_assignment_2824_; lean_object* v_lazyAssignment_2825_; lean_object* v_trees_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2836_; 
v_enabled_2823_ = lean_ctor_get_uint8(v_s_2822_, sizeof(void*)*3);
v_assignment_2824_ = lean_ctor_get(v_s_2822_, 0);
v_lazyAssignment_2825_ = lean_ctor_get(v_s_2822_, 1);
v_trees_2826_ = lean_ctor_get(v_s_2822_, 2);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_s_2822_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2828_ = v_s_2822_;
v_isShared_2829_ = v_isSharedCheck_2836_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_trees_2826_);
lean_inc(v_lazyAssignment_2825_);
lean_inc(v_assignment_2824_);
lean_dec(v_s_2822_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2836_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_val_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v_val_2830_ = lean_ctor_get(v_info_2820_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v_info_2820_, 1);
v___x_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_val_2830_);
lean_ctor_set(v___x_2831_, 1, v_trees_2826_);
v___x_2832_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2821_, v___x_2831_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 2, v___x_2832_);
v___x_2834_ = v___x_2828_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_assignment_2824_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_lazyAssignment_2825_);
lean_ctor_set(v_reuseFailAlloc_2835_, 2, v___x_2832_);
lean_ctor_set_uint8(v_reuseFailAlloc_2835_, sizeof(void*)*3, v_enabled_2823_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
uint8_t v_enabled_2837_; lean_object* v_assignment_2838_; lean_object* v_lazyAssignment_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2855_; 
v_enabled_2837_ = lean_ctor_get_uint8(v_s_2822_, sizeof(void*)*3);
v_assignment_2838_ = lean_ctor_get(v_s_2822_, 0);
v_lazyAssignment_2839_ = lean_ctor_get(v_s_2822_, 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_s_2822_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v_s_2822_, 2);
lean_dec(v_unused_2856_);
v___x_2841_ = v_s_2822_;
v_isShared_2842_ = v_isSharedCheck_2855_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_lazyAssignment_2839_);
lean_inc(v_assignment_2838_);
lean_dec(v_s_2822_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2855_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_val_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
v_val_2843_ = lean_ctor_get(v_info_2820_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_info_2820_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2845_ = v_info_2820_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_val_2843_);
lean_dec(v_info_2820_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 2);
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_val_2843_);
v___x_2848_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2849_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2821_, v___x_2848_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 2, v___x_2849_);
v___x_2851_ = v___x_2841_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_assignment_2838_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_lazyAssignment_2839_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v___x_2849_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*3, v_enabled_2837_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__2(lean_object* v_treesSaved_2857_, lean_object* v_modifyInfoState_2858_, lean_object* v_info_2859_){
_start:
{
lean_object* v___f_2860_; lean_object* v___x_2861_; 
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2860_, 0, v_info_2859_);
lean_closure_set(v___f_2860_, 1, v_treesSaved_2857_);
v___x_2861_ = lean_apply_1(v_modifyInfoState_2858_, v___f_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__3(lean_object* v___f_2862_, lean_object* v_info_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_apply_1(v___f_2862_, v_info_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__4(lean_object* v_toPure_2865_, lean_object* v_toBind_2866_, lean_object* v___f_2867_, lean_object* v_____do__lift_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_____do__lift_2868_);
v___x_2870_ = lean_apply_2(v_toPure_2865_, lean_box(0), v___x_2869_);
v___x_2871_ = lean_apply_4(v_toBind_2866_, lean_box(0), lean_box(0), v___x_2870_, v___f_2867_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__6(lean_object* v_toBind_2872_, lean_object* v_mkInfoOnError_2873_, lean_object* v___f_2874_, lean_object* v_mkInfo_2875_, lean_object* v___f_2876_, lean_object* v_a_x3f_2877_){
_start:
{
if (lean_obj_tag(v_a_x3f_2877_) == 0)
{
lean_object* v___x_2878_; 
lean_dec(v___f_2876_);
lean_dec(v_mkInfo_2875_);
v___x_2878_ = lean_apply_4(v_toBind_2872_, lean_box(0), lean_box(0), v_mkInfoOnError_2873_, v___f_2874_);
return v___x_2878_;
}
else
{
lean_object* v_val_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec(v___f_2874_);
lean_dec(v_mkInfoOnError_2873_);
v_val_2879_ = lean_ctor_get(v_a_x3f_2877_, 0);
lean_inc(v_val_2879_);
lean_dec_ref_known(v_a_x3f_2877_, 1);
v___x_2880_ = lean_apply_1(v_mkInfo_2875_, v_val_2879_);
v___x_2881_ = lean_apply_4(v_toBind_2872_, lean_box(0), lean_box(0), v___x_2880_, v___f_2876_);
return v___x_2881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__5(lean_object* v_toApplicative_2882_, lean_object* v_modifyInfoState_2883_, lean_object* v_toBind_2884_, lean_object* v_mkInfoOnError_2885_, lean_object* v_mkInfo_2886_, lean_object* v_inst_2887_, lean_object* v_x_2888_, lean_object* v___f_2889_, lean_object* v_treesSaved_2890_){
_start:
{
lean_object* v_toFunctor_2891_; lean_object* v_toPure_2892_; lean_object* v_map_2893_; lean_object* v___f_2894_; lean_object* v___f_2895_; lean_object* v___f_2896_; lean_object* v___f_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_toFunctor_2891_ = lean_ctor_get(v_toApplicative_2882_, 0);
lean_inc_ref(v_toFunctor_2891_);
v_toPure_2892_ = lean_ctor_get(v_toApplicative_2882_, 1);
lean_inc(v_toPure_2892_);
lean_dec_ref(v_toApplicative_2882_);
v_map_2893_ = lean_ctor_get(v_toFunctor_2891_, 0);
lean_inc(v_map_2893_);
lean_dec_ref(v_toFunctor_2891_);
v___f_2894_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2894_, 0, v_treesSaved_2890_);
lean_closure_set(v___f_2894_, 1, v_modifyInfoState_2883_);
v___f_2895_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2895_, 0, v___f_2894_);
lean_inc_ref(v___f_2895_);
lean_inc(v_toBind_2884_);
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_2896_, 0, v_toPure_2892_);
lean_closure_set(v___f_2896_, 1, v_toBind_2884_);
lean_closure_set(v___f_2896_, 2, v___f_2895_);
v___f_2897_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__6), 6, 5);
lean_closure_set(v___f_2897_, 0, v_toBind_2884_);
lean_closure_set(v___f_2897_, 1, v_mkInfoOnError_2885_);
lean_closure_set(v___f_2897_, 2, v___f_2896_);
lean_closure_set(v___f_2897_, 3, v_mkInfo_2886_);
lean_closure_set(v___f_2897_, 4, v___f_2895_);
v___x_2898_ = lean_apply_4(v_inst_2887_, lean_box(0), lean_box(0), v_x_2888_, v___f_2897_);
v___x_2899_ = lean_apply_4(v_map_2893_, lean_box(0), lean_box(0), v___f_2889_, v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7(lean_object* v_x_2900_, lean_object* v_inst_2901_, lean_object* v_inst_2902_, lean_object* v_toBind_2903_, lean_object* v___f_2904_, lean_object* v_____do__lift_2905_){
_start:
{
uint8_t v_enabled_2906_; 
v_enabled_2906_ = lean_ctor_get_uint8(v_____do__lift_2905_, sizeof(void*)*3);
if (v_enabled_2906_ == 0)
{
lean_dec(v___f_2904_);
lean_dec(v_toBind_2903_);
lean_dec_ref(v_inst_2902_);
lean_dec_ref(v_inst_2901_);
lean_inc(v_x_2900_);
return v_x_2900_;
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = l_Lean_Elab_getResetInfoTrees___redArg(v_inst_2901_, v_inst_2902_);
v___x_2908_ = lean_apply_4(v_toBind_2903_, lean_box(0), lean_box(0), v___x_2907_, v___f_2904_);
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed(lean_object* v_x_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_toBind_2912_, lean_object* v___f_2913_, lean_object* v_____do__lift_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_Elab_withInfoContext_x27___redArg___lam__7(v_x_2909_, v_inst_2910_, v_inst_2911_, v_toBind_2912_, v___f_2913_, v_____do__lift_2914_);
lean_dec_ref(v_____do__lift_2914_);
lean_dec(v_x_2909_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___redArg(lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_x_2920_, lean_object* v_mkInfo_2921_, lean_object* v_mkInfoOnError_2922_){
_start:
{
lean_object* v_toApplicative_2923_; lean_object* v_toBind_2924_; lean_object* v_getInfoState_2925_; lean_object* v_modifyInfoState_2926_; lean_object* v___f_2927_; lean_object* v___f_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; 
v_toApplicative_2923_ = lean_ctor_get(v_inst_2917_, 0);
v_toBind_2924_ = lean_ctor_get(v_inst_2917_, 1);
lean_inc_n(v_toBind_2924_, 3);
v_getInfoState_2925_ = lean_ctor_get(v_inst_2918_, 0);
lean_inc(v_getInfoState_2925_);
v_modifyInfoState_2926_ = lean_ctor_get(v_inst_2918_, 1);
v___f_2927_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2920_);
lean_inc(v_modifyInfoState_2926_);
lean_inc_ref(v_toApplicative_2923_);
v___f_2928_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2928_, 0, v_toApplicative_2923_);
lean_closure_set(v___f_2928_, 1, v_modifyInfoState_2926_);
lean_closure_set(v___f_2928_, 2, v_toBind_2924_);
lean_closure_set(v___f_2928_, 3, v_mkInfoOnError_2922_);
lean_closure_set(v___f_2928_, 4, v_mkInfo_2921_);
lean_closure_set(v___f_2928_, 5, v_inst_2919_);
lean_closure_set(v___f_2928_, 6, v_x_2920_);
lean_closure_set(v___f_2928_, 7, v___f_2927_);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_2929_, 0, v_x_2920_);
lean_closure_set(v___f_2929_, 1, v_inst_2917_);
lean_closure_set(v___f_2929_, 2, v_inst_2918_);
lean_closure_set(v___f_2929_, 3, v_toBind_2924_);
lean_closure_set(v___f_2929_, 4, v___f_2928_);
v___x_2930_ = lean_apply_4(v_toBind_2924_, lean_box(0), lean_box(0), v_getInfoState_2925_, v___f_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* v_m_2931_, lean_object* v_inst_2932_, lean_object* v_inst_2933_, lean_object* v_00_u03b1_2934_, lean_object* v_inst_2935_, lean_object* v_x_2936_, lean_object* v_mkInfo_2937_, lean_object* v_mkInfoOnError_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Elab_withInfoContext_x27___redArg(v_inst_2932_, v_inst_2933_, v_inst_2935_, v_x_2936_, v_mkInfo_2937_, v_mkInfoOnError_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__1(lean_object* v_treesSaved_2940_, lean_object* v_tree_2941_, lean_object* v_s_2942_){
_start:
{
uint8_t v_enabled_2943_; lean_object* v_assignment_2944_; lean_object* v_lazyAssignment_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2953_; 
v_enabled_2943_ = lean_ctor_get_uint8(v_s_2942_, sizeof(void*)*3);
v_assignment_2944_ = lean_ctor_get(v_s_2942_, 0);
v_lazyAssignment_2945_ = lean_ctor_get(v_s_2942_, 1);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_s_2942_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; 
v_unused_2954_ = lean_ctor_get(v_s_2942_, 2);
lean_dec(v_unused_2954_);
v___x_2947_ = v_s_2942_;
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_lazyAssignment_2945_);
lean_inc(v_assignment_2944_);
lean_dec(v_s_2942_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = l_Lean_PersistentArray_push___redArg(v_treesSaved_2940_, v_tree_2941_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 2, v___x_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_assignment_2944_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_lazyAssignment_2945_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v___x_2949_);
lean_ctor_set_uint8(v_reuseFailAlloc_2952_, sizeof(void*)*3, v_enabled_2943_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__0(lean_object* v_treesSaved_2955_, lean_object* v_modifyInfoState_2956_, lean_object* v_tree_2957_){
_start:
{
lean_object* v___f_2958_; lean_object* v___x_2959_; 
v___f_2958_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2958_, 0, v_treesSaved_2955_);
lean_closure_set(v___f_2958_, 1, v_tree_2957_);
v___x_2959_ = lean_apply_1(v_modifyInfoState_2956_, v___f_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__2(lean_object* v_mkInfoTree_2960_, lean_object* v_toBind_2961_, lean_object* v___f_2962_, lean_object* v_st_2963_){
_start:
{
lean_object* v_trees_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_trees_2964_ = lean_ctor_get(v_st_2963_, 2);
lean_inc_ref(v_trees_2964_);
lean_dec_ref(v_st_2963_);
v___x_2965_ = lean_apply_1(v_mkInfoTree_2960_, v_trees_2964_);
v___x_2966_ = lean_apply_4(v_toBind_2961_, lean_box(0), lean_box(0), v___x_2965_, v___f_2962_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3(lean_object* v_toBind_2967_, lean_object* v_getInfoState_2968_, lean_object* v___f_2969_, lean_object* v_x_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v_getInfoState_2968_, v___f_2969_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed(lean_object* v_toBind_2972_, lean_object* v_getInfoState_2973_, lean_object* v___f_2974_, lean_object* v_x_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_Elab_withInfoTreeContext___redArg___lam__3(v_toBind_2972_, v_getInfoState_2973_, v___f_2974_, v_x_2975_);
lean_dec(v_x_2975_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg___lam__4(lean_object* v_toApplicative_2977_, lean_object* v_modifyInfoState_2978_, lean_object* v_mkInfoTree_2979_, lean_object* v_toBind_2980_, lean_object* v_getInfoState_2981_, lean_object* v_inst_2982_, lean_object* v_x_2983_, lean_object* v___f_2984_, lean_object* v_treesSaved_2985_){
_start:
{
lean_object* v_toFunctor_2986_; lean_object* v_map_2987_; lean_object* v___f_2988_; lean_object* v___f_2989_; lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_toFunctor_2986_ = lean_ctor_get(v_toApplicative_2977_, 0);
lean_inc_ref(v_toFunctor_2986_);
lean_dec_ref(v_toApplicative_2977_);
v_map_2987_ = lean_ctor_get(v_toFunctor_2986_, 0);
lean_inc(v_map_2987_);
lean_dec_ref(v_toFunctor_2986_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2988_, 0, v_treesSaved_2985_);
lean_closure_set(v___f_2988_, 1, v_modifyInfoState_2978_);
lean_inc(v_toBind_2980_);
v___f_2989_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2989_, 0, v_mkInfoTree_2979_);
lean_closure_set(v___f_2989_, 1, v_toBind_2980_);
lean_closure_set(v___f_2989_, 2, v___f_2988_);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2990_, 0, v_toBind_2980_);
lean_closure_set(v___f_2990_, 1, v_getInfoState_2981_);
lean_closure_set(v___f_2990_, 2, v___f_2989_);
v___x_2991_ = lean_apply_4(v_inst_2982_, lean_box(0), lean_box(0), v_x_2983_, v___f_2990_);
v___x_2992_ = lean_apply_4(v_map_2987_, lean_box(0), lean_box(0), v___f_2984_, v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_inst_2995_, lean_object* v_x_2996_, lean_object* v_mkInfoTree_2997_){
_start:
{
lean_object* v_toApplicative_2998_; lean_object* v_toBind_2999_; lean_object* v_getInfoState_3000_; lean_object* v_modifyInfoState_3001_; lean_object* v___f_3002_; lean_object* v___f_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; 
v_toApplicative_2998_ = lean_ctor_get(v_inst_2993_, 0);
v_toBind_2999_ = lean_ctor_get(v_inst_2993_, 1);
lean_inc_n(v_toBind_2999_, 3);
v_getInfoState_3000_ = lean_ctor_get(v_inst_2994_, 0);
lean_inc_n(v_getInfoState_3000_, 2);
v_modifyInfoState_3001_ = lean_ctor_get(v_inst_2994_, 1);
v___f_3002_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_2996_);
lean_inc(v_modifyInfoState_3001_);
lean_inc_ref(v_toApplicative_2998_);
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__4), 9, 8);
lean_closure_set(v___f_3003_, 0, v_toApplicative_2998_);
lean_closure_set(v___f_3003_, 1, v_modifyInfoState_3001_);
lean_closure_set(v___f_3003_, 2, v_mkInfoTree_2997_);
lean_closure_set(v___f_3003_, 3, v_toBind_2999_);
lean_closure_set(v___f_3003_, 4, v_getInfoState_3000_);
lean_closure_set(v___f_3003_, 5, v_inst_2995_);
lean_closure_set(v___f_3003_, 6, v_x_2996_);
lean_closure_set(v___f_3003_, 7, v___f_3002_);
v___f_3004_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3004_, 0, v_x_2996_);
lean_closure_set(v___f_3004_, 1, v_inst_2993_);
lean_closure_set(v___f_3004_, 2, v_inst_2994_);
lean_closure_set(v___f_3004_, 3, v_toBind_2999_);
lean_closure_set(v___f_3004_, 4, v___f_3003_);
v___x_3005_ = lean_apply_4(v_toBind_2999_, lean_box(0), lean_box(0), v_getInfoState_3000_, v___f_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext(lean_object* v_m_3006_, lean_object* v_inst_3007_, lean_object* v_inst_3008_, lean_object* v_00_u03b1_3009_, lean_object* v_inst_3010_, lean_object* v_x_3011_, lean_object* v_mkInfoTree_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3007_, v_inst_3008_, v_inst_3010_, v_x_3011_, v_mkInfoTree_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__0(lean_object* v_trees_3014_, lean_object* v_toPure_3015_, lean_object* v_____do__lift_3016_){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3017_, 0, v_____do__lift_3016_);
lean_ctor_set(v___x_3017_, 1, v_trees_3014_);
v___x_3018_ = lean_apply_2(v_toPure_3015_, lean_box(0), v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg___lam__1(lean_object* v_toPure_3019_, lean_object* v_toBind_3020_, lean_object* v_mkInfo_3021_, lean_object* v_trees_3022_){
_start:
{
lean_object* v___f_3023_; lean_object* v___x_3024_; 
v___f_3023_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3023_, 0, v_trees_3022_);
lean_closure_set(v___f_3023_, 1, v_toPure_3019_);
v___x_3024_ = lean_apply_4(v_toBind_3020_, lean_box(0), lean_box(0), v_mkInfo_3021_, v___f_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext___redArg(lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_inst_3027_, lean_object* v_x_3028_, lean_object* v_mkInfo_3029_){
_start:
{
lean_object* v_toApplicative_3030_; lean_object* v_toBind_3031_; lean_object* v_toPure_3032_; lean_object* v___f_3033_; lean_object* v___x_3034_; 
v_toApplicative_3030_ = lean_ctor_get(v_inst_3025_, 0);
v_toBind_3031_ = lean_ctor_get(v_inst_3025_, 1);
v_toPure_3032_ = lean_ctor_get(v_toApplicative_3030_, 1);
lean_inc(v_toBind_3031_);
lean_inc(v_toPure_3032_);
v___f_3033_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3033_, 0, v_toPure_3032_);
lean_closure_set(v___f_3033_, 1, v_toBind_3031_);
lean_closure_set(v___f_3033_, 2, v_mkInfo_3029_);
v___x_3034_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3025_, v_inst_3026_, v_inst_3027_, v_x_3028_, v___f_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext(lean_object* v_m_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_00_u03b1_3038_, lean_object* v_inst_3039_, lean_object* v_x_3040_, lean_object* v_mkInfo_3041_){
_start:
{
lean_object* v_toApplicative_3042_; lean_object* v_toBind_3043_; lean_object* v_toPure_3044_; lean_object* v___f_3045_; lean_object* v___x_3046_; 
v_toApplicative_3042_ = lean_ctor_get(v_inst_3036_, 0);
v_toBind_3043_ = lean_ctor_get(v_inst_3036_, 1);
v_toPure_3044_ = lean_ctor_get(v_toApplicative_3042_, 1);
lean_inc(v_toBind_3043_);
lean_inc(v_toPure_3044_);
v___f_3045_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3045_, 0, v_toPure_3044_);
lean_closure_set(v___f_3045_, 1, v_toBind_3043_);
lean_closure_set(v___f_3045_, 2, v_mkInfo_3041_);
v___x_3046_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3036_, v_inst_3037_, v_inst_3039_, v_x_3040_, v___f_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(lean_object* v_treesSaved_3047_, lean_object* v_trees_3048_, lean_object* v_s_3049_){
_start:
{
uint8_t v_enabled_3050_; lean_object* v_assignment_3051_; lean_object* v_lazyAssignment_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3060_; 
v_enabled_3050_ = lean_ctor_get_uint8(v_s_3049_, sizeof(void*)*3);
v_assignment_3051_ = lean_ctor_get(v_s_3049_, 0);
v_lazyAssignment_3052_ = lean_ctor_get(v_s_3049_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_s_3049_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v_s_3049_, 2);
lean_dec(v_unused_3061_);
v___x_3054_ = v_s_3049_;
v_isShared_3055_ = v_isSharedCheck_3060_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_lazyAssignment_3052_);
lean_inc(v_assignment_3051_);
lean_dec(v_s_3049_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3060_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3056_ = l_Lean_PersistentArray_append___redArg(v_treesSaved_3047_, v_trees_3048_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 2, v___x_3056_);
v___x_3058_ = v___x_3054_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_assignment_3051_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_lazyAssignment_3052_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v___x_3056_);
lean_ctor_set_uint8(v_reuseFailAlloc_3059_, sizeof(void*)*3, v_enabled_3050_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed(lean_object* v_treesSaved_3062_, lean_object* v_trees_3063_, lean_object* v_s_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1(v_treesSaved_3062_, v_trees_3063_, v_s_3064_);
lean_dec_ref(v_trees_3063_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0(lean_object* v_treesSaved_3066_, lean_object* v_modifyInfoState_3067_, lean_object* v_trees_3068_){
_start:
{
lean_object* v___f_3069_; lean_object* v___x_3070_; 
v___f_3069_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3069_, 0, v_treesSaved_3066_);
lean_closure_set(v___f_3069_, 1, v_trees_3068_);
v___x_3070_ = lean_apply_1(v_modifyInfoState_3067_, v___f_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(lean_object* v_toPure_3071_, lean_object* v_tree_3072_, lean_object* v_____do__lift_3073_){
_start:
{
if (lean_obj_tag(v_____do__lift_3073_) == 0)
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_apply_2(v_toPure_3071_, lean_box(0), v_tree_3072_);
return v___x_3074_;
}
else
{
lean_object* v_val_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_val_3075_ = lean_ctor_get(v_____do__lift_3073_, 0);
lean_inc(v_val_3075_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v_val_3075_);
lean_ctor_set(v___x_3076_, 1, v_tree_3072_);
v___x_3077_ = lean_apply_2(v_toPure_3071_, lean_box(0), v___x_3076_);
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed(lean_object* v_toPure_3078_, lean_object* v_tree_3079_, lean_object* v_____do__lift_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2(v_toPure_3078_, v_tree_3079_, v_____do__lift_3080_);
lean_dec(v_____do__lift_3080_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(lean_object* v_assignment_3082_, lean_object* v_toPure_3083_, lean_object* v_toBind_3084_, lean_object* v_ctx_x3f_3085_, lean_object* v_tree_3086_){
_start:
{
lean_object* v_tree_3087_; lean_object* v___f_3088_; lean_object* v___x_3089_; 
v_tree_3087_ = l_Lean_Elab_InfoTree_substitute(v_tree_3086_, v_assignment_3082_);
v___f_3088_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3088_, 0, v_toPure_3083_);
lean_closure_set(v___f_3088_, 1, v_tree_3087_);
v___x_3089_ = lean_apply_4(v_toBind_3084_, lean_box(0), lean_box(0), v_ctx_x3f_3085_, v___f_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed(lean_object* v_assignment_3090_, lean_object* v_toPure_3091_, lean_object* v_toBind_3092_, lean_object* v_ctx_x3f_3093_, lean_object* v_tree_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3(v_assignment_3090_, v_toPure_3091_, v_toBind_3092_, v_ctx_x3f_3093_, v_tree_3094_);
lean_dec_ref(v_assignment_3090_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4(lean_object* v_toPure_3096_, lean_object* v_toBind_3097_, lean_object* v_ctx_x3f_3098_, lean_object* v_inst_3099_, lean_object* v___f_3100_, lean_object* v_st_3101_){
_start:
{
lean_object* v_assignment_3102_; lean_object* v_trees_3103_; lean_object* v___f_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_assignment_3102_ = lean_ctor_get(v_st_3101_, 0);
lean_inc_ref(v_assignment_3102_);
v_trees_3103_ = lean_ctor_get(v_st_3101_, 2);
lean_inc_ref(v_trees_3103_);
lean_dec_ref(v_st_3101_);
lean_inc(v_toBind_3097_);
v___f_3104_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3104_, 0, v_assignment_3102_);
lean_closure_set(v___f_3104_, 1, v_toPure_3096_);
lean_closure_set(v___f_3104_, 2, v_toBind_3097_);
lean_closure_set(v___f_3104_, 3, v_ctx_x3f_3098_);
v___x_3105_ = l_Lean_PersistentArray_mapM___redArg(v_inst_3099_, v___f_3104_, v_trees_3103_);
v___x_3106_ = lean_apply_4(v_toBind_3097_, lean_box(0), lean_box(0), v___x_3105_, v___f_3100_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6(lean_object* v_toApplicative_3107_, lean_object* v_modifyInfoState_3108_, lean_object* v_toBind_3109_, lean_object* v_ctx_x3f_3110_, lean_object* v_inst_3111_, lean_object* v_getInfoState_3112_, lean_object* v_inst_3113_, lean_object* v_x_3114_, lean_object* v___f_3115_, lean_object* v_treesSaved_3116_){
_start:
{
lean_object* v_toFunctor_3117_; lean_object* v_toPure_3118_; lean_object* v_map_3119_; lean_object* v___f_3120_; lean_object* v___f_3121_; lean_object* v___f_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_toFunctor_3117_ = lean_ctor_get(v_toApplicative_3107_, 0);
lean_inc_ref(v_toFunctor_3117_);
v_toPure_3118_ = lean_ctor_get(v_toApplicative_3107_, 1);
lean_inc(v_toPure_3118_);
lean_dec_ref(v_toApplicative_3107_);
v_map_3119_ = lean_ctor_get(v_toFunctor_3117_, 0);
lean_inc(v_map_3119_);
lean_dec_ref(v_toFunctor_3117_);
v___f_3120_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3120_, 0, v_treesSaved_3116_);
lean_closure_set(v___f_3120_, 1, v_modifyInfoState_3108_);
lean_inc(v_toBind_3109_);
v___f_3121_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3121_, 0, v_toPure_3118_);
lean_closure_set(v___f_3121_, 1, v_toBind_3109_);
lean_closure_set(v___f_3121_, 2, v_ctx_x3f_3110_);
lean_closure_set(v___f_3121_, 3, v_inst_3111_);
lean_closure_set(v___f_3121_, 4, v___f_3120_);
v___f_3122_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoTreeContext___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3122_, 0, v_toBind_3109_);
lean_closure_set(v___f_3122_, 1, v_getInfoState_3112_);
lean_closure_set(v___f_3122_, 2, v___f_3121_);
v___x_3123_ = lean_apply_4(v_inst_3113_, lean_box(0), lean_box(0), v_x_3114_, v___f_3122_);
v___x_3124_ = lean_apply_4(v_map_3119_, lean_box(0), lean_box(0), v___f_3115_, v___x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(lean_object* v_inst_3125_, lean_object* v_inst_3126_, lean_object* v_inst_3127_, lean_object* v_x_3128_, lean_object* v_ctx_x3f_3129_){
_start:
{
lean_object* v_toApplicative_3130_; lean_object* v_toBind_3131_; lean_object* v_getInfoState_3132_; lean_object* v_modifyInfoState_3133_; lean_object* v___f_3134_; lean_object* v___f_3135_; lean_object* v___f_3136_; lean_object* v___x_3137_; 
v_toApplicative_3130_ = lean_ctor_get(v_inst_3125_, 0);
v_toBind_3131_ = lean_ctor_get(v_inst_3125_, 1);
lean_inc_n(v_toBind_3131_, 3);
v_getInfoState_3132_ = lean_ctor_get(v_inst_3126_, 0);
lean_inc_n(v_getInfoState_3132_, 2);
v_modifyInfoState_3133_ = lean_ctor_get(v_inst_3126_, 1);
v___f_3134_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3128_);
lean_inc_ref(v_inst_3125_);
lean_inc(v_modifyInfoState_3133_);
lean_inc_ref(v_toApplicative_3130_);
v___f_3135_ = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg___lam__6), 10, 9);
lean_closure_set(v___f_3135_, 0, v_toApplicative_3130_);
lean_closure_set(v___f_3135_, 1, v_modifyInfoState_3133_);
lean_closure_set(v___f_3135_, 2, v_toBind_3131_);
lean_closure_set(v___f_3135_, 3, v_ctx_x3f_3129_);
lean_closure_set(v___f_3135_, 4, v_inst_3125_);
lean_closure_set(v___f_3135_, 5, v_getInfoState_3132_);
lean_closure_set(v___f_3135_, 6, v_inst_3127_);
lean_closure_set(v___f_3135_, 7, v_x_3128_);
lean_closure_set(v___f_3135_, 8, v___f_3134_);
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3136_, 0, v_x_3128_);
lean_closure_set(v___f_3136_, 1, v_inst_3125_);
lean_closure_set(v___f_3136_, 2, v_inst_3126_);
lean_closure_set(v___f_3136_, 3, v_toBind_3131_);
lean_closure_set(v___f_3136_, 4, v___f_3135_);
v___x_3137_ = lean_apply_4(v_toBind_3131_, lean_box(0), lean_box(0), v_getInfoState_3132_, v___f_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext(lean_object* v_m_3138_, lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_00_u03b1_3141_, lean_object* v_inst_3142_, lean_object* v_x_3143_, lean_object* v_ctx_x3f_3144_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3139_, v_inst_3140_, v_inst_3142_, v_x_3143_, v_ctx_x3f_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg___lam__0(lean_object* v_toPure_3146_, lean_object* v_____do__lift_3147_){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_____do__lift_3147_);
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
v___x_3150_ = lean_apply_2(v_toPure_3146_, lean_box(0), v___x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___redArg(lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_inst_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_x_3160_){
_start:
{
lean_object* v_toApplicative_3161_; lean_object* v_toBind_3162_; lean_object* v_toPure_3163_; lean_object* v___x_3164_; lean_object* v___f_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_toApplicative_3161_ = lean_ctor_get(v_inst_3151_, 0);
v_toBind_3162_ = lean_ctor_get(v_inst_3151_, 1);
v_toPure_3163_ = lean_ctor_get(v_toApplicative_3161_, 1);
lean_inc_ref(v_inst_3151_);
v___x_3164_ = l_Lean_Elab_CommandContextInfo_save___redArg(v_inst_3151_, v_inst_3155_, v_inst_3157_, v_inst_3156_, v_inst_3158_, v_inst_3153_, v_inst_3159_);
lean_inc(v_toPure_3163_);
v___f_3165_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3165_, 0, v_toPure_3163_);
lean_inc(v_toBind_3162_);
v___x_3166_ = lean_apply_4(v_toBind_3162_, lean_box(0), lean_box(0), v___x_3164_, v___f_3165_);
v___x_3167_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3151_, v_inst_3152_, v_inst_3154_, v_x_3160_, v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext(lean_object* v_m_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_00_u03b1_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_x_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Elab_withSaveInfoContext___redArg(v_inst_3169_, v_inst_3170_, v_inst_3172_, v_inst_3173_, v_inst_3174_, v_inst_3175_, v_inst_3176_, v_inst_3177_, v_inst_3178_, v_x_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0(lean_object* v_toPure_3181_, lean_object* v_____x_3182_){
_start:
{
if (lean_obj_tag(v_____x_3182_) == 1)
{
lean_object* v_val_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3192_; 
v_val_3183_ = lean_ctor_get(v_____x_3182_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_____x_3182_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3185_ = v_____x_3182_;
v_isShared_3186_ = v_isSharedCheck_3192_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_val_3183_);
lean_dec(v_____x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3192_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_val_3183_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3189_ = v___x_3185_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_apply_2(v_toPure_3181_, lean_box(0), v___x_3189_);
return v___x_3190_;
}
}
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_dec(v_____x_3182_);
v___x_3193_ = lean_box(0);
v___x_3194_ = lean_apply_2(v_toPure_3181_, lean_box(0), v___x_3193_);
return v___x_3194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext___redArg(lean_object* v_inst_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v_toApplicative_3200_; lean_object* v_toBind_3201_; lean_object* v_toPure_3202_; lean_object* v___f_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_toApplicative_3200_ = lean_ctor_get(v_inst_3195_, 0);
v_toBind_3201_ = lean_ctor_get(v_inst_3195_, 1);
v_toPure_3202_ = lean_ctor_get(v_toApplicative_3200_, 1);
lean_inc(v_toPure_3202_);
v___f_3203_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveParentDeclInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3203_, 0, v_toPure_3202_);
lean_inc(v_toBind_3201_);
v___x_3204_ = lean_apply_4(v_toBind_3201_, lean_box(0), lean_box(0), v_inst_3198_, v___f_3203_);
v___x_3205_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3195_, v_inst_3196_, v_inst_3197_, v_x_3199_, v___x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveParentDeclInfoContext(lean_object* v_m_3206_, lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_00_u03b1_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Elab_withSaveParentDeclInfoContext___redArg(v_inst_3207_, v_inst_3208_, v_inst_3210_, v_inst_3211_, v_x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0(lean_object* v_toPure_3214_, lean_object* v_autoImplicits_3215_){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3216_, 0, v_autoImplicits_3215_);
v___x_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
v___x_3218_ = lean_apply_2(v_toPure_3214_, lean_box(0), v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(lean_object* v_inst_3219_, lean_object* v_inst_3220_, lean_object* v_inst_3221_, lean_object* v_inst_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v_toApplicative_3224_; lean_object* v_toBind_3225_; lean_object* v_toPure_3226_; lean_object* v___f_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v_toApplicative_3224_ = lean_ctor_get(v_inst_3219_, 0);
v_toBind_3225_ = lean_ctor_get(v_inst_3219_, 1);
v_toPure_3226_ = lean_ctor_get(v_toApplicative_3224_, 1);
lean_inc(v_toPure_3226_);
v___f_3227_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3227_, 0, v_toPure_3226_);
lean_inc(v_toBind_3225_);
v___x_3228_ = lean_apply_4(v_toBind_3225_, lean_box(0), lean_box(0), v_inst_3222_, v___f_3227_);
v___x_3229_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___redArg(v_inst_3219_, v_inst_3220_, v_inst_3221_, v_x_3223_, v___x_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveAutoImplicitInfoContext(lean_object* v_m_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_00_u03b1_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_x_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_Elab_withSaveAutoImplicitInfoContext___redArg(v_inst_3231_, v_inst_3232_, v_inst_3234_, v_inst_3235_, v_x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(lean_object* v___x_3238_, lean_object* v___x_3239_, lean_object* v_mvarId_3240_, lean_object* v_toPure_3241_, lean_object* v_____do__lift_3242_){
_start:
{
lean_object* v_assignment_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_assignment_3243_ = lean_ctor_get(v_____do__lift_3242_, 0);
v___x_3244_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3238_, v___x_3239_, v_assignment_3243_, v_mvarId_3240_);
v___x_3245_ = lean_apply_2(v_toPure_3241_, lean_box(0), v___x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed(lean_object* v___x_3246_, lean_object* v___x_3247_, lean_object* v_mvarId_3248_, lean_object* v_toPure_3249_, lean_object* v_____do__lift_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0(v___x_3246_, v___x_3247_, v_mvarId_3248_, v_toPure_3249_, v_____do__lift_3250_);
lean_dec_ref(v_____do__lift_3250_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(lean_object* v_inst_3254_, lean_object* v_inst_3255_, lean_object* v_mvarId_3256_){
_start:
{
lean_object* v_toApplicative_3257_; lean_object* v_toBind_3258_; lean_object* v_getInfoState_3259_; lean_object* v_toPure_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___f_3263_; lean_object* v___x_3264_; 
v_toApplicative_3257_ = lean_ctor_get(v_inst_3254_, 0);
lean_inc_ref(v_toApplicative_3257_);
v_toBind_3258_ = lean_ctor_get(v_inst_3254_, 1);
lean_inc(v_toBind_3258_);
lean_dec_ref(v_inst_3254_);
v_getInfoState_3259_ = lean_ctor_get(v_inst_3255_, 0);
lean_inc(v_getInfoState_3259_);
lean_dec_ref(v_inst_3255_);
v_toPure_3260_ = lean_ctor_get(v_toApplicative_3257_, 1);
lean_inc(v_toPure_3260_);
lean_dec_ref(v_toApplicative_3257_);
v___x_3261_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3262_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___f_3263_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3263_, 0, v___x_3261_);
lean_closure_set(v___f_3263_, 1, v___x_3262_);
lean_closure_set(v___f_3263_, 2, v_mvarId_3256_);
lean_closure_set(v___f_3263_, 3, v_toPure_3260_);
v___x_3264_ = lean_apply_4(v_toBind_3258_, lean_box(0), lean_box(0), v_getInfoState_3259_, v___f_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* v_m_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_mvarId_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3266_, v_inst_3267_, v_mvarId_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__0(lean_object* v_mvarId_3270_, lean_object* v_infoTree_3271_, lean_object* v_s_3272_){
_start:
{
uint8_t v_enabled_3273_; lean_object* v_assignment_3274_; lean_object* v_lazyAssignment_3275_; lean_object* v_trees_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3286_; 
v_enabled_3273_ = lean_ctor_get_uint8(v_s_3272_, sizeof(void*)*3);
v_assignment_3274_ = lean_ctor_get(v_s_3272_, 0);
v_lazyAssignment_3275_ = lean_ctor_get(v_s_3272_, 1);
v_trees_3276_ = lean_ctor_get(v_s_3272_, 2);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_s_3272_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3278_ = v_s_3272_;
v_isShared_3279_ = v_isSharedCheck_3286_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_trees_3276_);
lean_inc(v_lazyAssignment_3275_);
lean_inc(v_assignment_3274_);
lean_dec(v_s_3272_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3286_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3280_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3281_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3282_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3280_, v___x_3281_, v_assignment_3274_, v_mvarId_3270_, v_infoTree_3271_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3282_);
v___x_3284_ = v___x_3278_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_lazyAssignment_3275_);
lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_trees_3276_);
lean_ctor_set_uint8(v_reuseFailAlloc_3285_, sizeof(void*)*3, v_enabled_3273_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3290_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__2));
v___x_3291_ = lean_unsigned_to_nat(2u);
v___x_3292_ = lean_unsigned_to_nat(384u);
v___x_3293_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__1));
v___x_3294_ = ((lean_object*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__0));
v___x_3295_ = l_mkPanicMessageWithDecl(v___x_3294_, v___x_3293_, v___x_3292_, v___x_3291_, v___x_3290_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1(lean_object* v_inst_3296_, lean_object* v___f_3297_, lean_object* v_inst_3298_, lean_object* v_____do__lift_3299_){
_start:
{
if (lean_obj_tag(v_____do__lift_3299_) == 0)
{
lean_object* v_modifyInfoState_3300_; lean_object* v___x_3301_; 
lean_dec_ref(v_inst_3298_);
v_modifyInfoState_3300_ = lean_ctor_get(v_inst_3296_, 1);
lean_inc(v_modifyInfoState_3300_);
lean_dec_ref(v_inst_3296_);
v___x_3301_ = lean_apply_1(v_modifyInfoState_3300_, v___f_3297_);
return v___x_3301_;
}
else
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec_ref(v___f_3297_);
lean_dec_ref(v_inst_3296_);
v___x_3302_ = lean_box(0);
v___x_3303_ = l_instInhabitedOfMonad___redArg(v_inst_3298_, v___x_3302_);
v___x_3304_ = lean_obj_once(&l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3, &l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_assignInfoHoleId___redArg___lam__1___closed__3);
v___x_3305_ = l_panic___redArg(v___x_3303_, v___x_3304_);
lean_dec(v___x_3303_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed(lean_object* v_inst_3306_, lean_object* v___f_3307_, lean_object* v_inst_3308_, lean_object* v_____do__lift_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Elab_assignInfoHoleId___redArg___lam__1(v_inst_3306_, v___f_3307_, v_inst_3308_, v_____do__lift_3309_);
lean_dec(v_____do__lift_3309_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId___redArg(lean_object* v_inst_3311_, lean_object* v_inst_3312_, lean_object* v_mvarId_3313_, lean_object* v_infoTree_3314_){
_start:
{
lean_object* v_toBind_3315_; lean_object* v___f_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_toBind_3315_ = lean_ctor_get(v_inst_3311_, 1);
lean_inc(v_toBind_3315_);
lean_inc(v_mvarId_3313_);
v___f_3316_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3316_, 0, v_mvarId_3313_);
lean_closure_set(v___f_3316_, 1, v_infoTree_3314_);
lean_inc_ref(v_inst_3311_);
lean_inc_ref(v_inst_3312_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3317_, 0, v_inst_3312_);
lean_closure_set(v___f_3317_, 1, v___f_3316_);
lean_closure_set(v___f_3317_, 2, v_inst_3311_);
v___x_3318_ = l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg(v_inst_3311_, v_inst_3312_, v_mvarId_3313_);
v___x_3319_ = lean_apply_4(v_toBind_3315_, lean_box(0), lean_box(0), v___x_3318_, v___f_3317_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* v_m_3320_, lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_mvarId_3323_, lean_object* v_infoTree_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Lean_Elab_assignInfoHoleId___redArg(v_inst_3321_, v_inst_3322_, v_mvarId_3323_, v_infoTree_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0(lean_object* v_stx_3326_, lean_object* v_output_3327_, lean_object* v_toPure_3328_, lean_object* v_____do__lift_3329_){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3330_, 0, v_____do__lift_3329_);
lean_ctor_set(v___x_3330_, 1, v_stx_3326_);
lean_ctor_set(v___x_3330_, 2, v_output_3327_);
v___x_3331_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
v___x_3332_ = lean_apply_2(v_toPure_3328_, lean_box(0), v___x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_inst_3336_, lean_object* v_stx_3337_, lean_object* v_output_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v_toApplicative_3340_; lean_object* v_toBind_3341_; lean_object* v_toPure_3342_; lean_object* v___f_3343_; lean_object* v_mkInfo_3344_; lean_object* v___f_3345_; lean_object* v___x_3346_; 
v_toApplicative_3340_ = lean_ctor_get(v_inst_3334_, 0);
v_toBind_3341_ = lean_ctor_get(v_inst_3334_, 1);
v_toPure_3342_ = lean_ctor_get(v_toApplicative_3340_, 1);
lean_inc_n(v_toPure_3342_, 2);
v___f_3343_ = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3343_, 0, v_stx_3337_);
lean_closure_set(v___f_3343_, 1, v_output_3338_);
lean_closure_set(v___f_3343_, 2, v_toPure_3342_);
lean_inc_n(v_toBind_3341_, 2);
v_mkInfo_3344_ = lean_apply_4(v_toBind_3341_, lean_box(0), lean_box(0), v_inst_3336_, v___f_3343_);
v___f_3345_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3345_, 0, v_toPure_3342_);
lean_closure_set(v___f_3345_, 1, v_toBind_3341_);
lean_closure_set(v___f_3345_, 2, v_mkInfo_3344_);
v___x_3346_ = l_Lean_Elab_withInfoTreeContext___redArg(v_inst_3334_, v_inst_3335_, v_inst_3333_, v_x_3339_, v___f_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* v_m_3347_, lean_object* v_00_u03b1_3348_, lean_object* v_inst_3349_, lean_object* v_inst_3350_, lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_stx_3353_, lean_object* v_output_3354_, lean_object* v_x_3355_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_Elab_withMacroExpansionInfo___redArg(v_inst_3349_, v_inst_3350_, v_inst_3351_, v_inst_3352_, v_stx_3353_, v_output_3354_, v_x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__1(lean_object* v_treesSaved_3357_, lean_object* v_mvarId_3358_, lean_object* v_s_3359_){
_start:
{
lean_object* v_trees_3360_; uint8_t v_enabled_3361_; lean_object* v_assignment_3362_; lean_object* v_lazyAssignment_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3383_; 
v_trees_3360_ = lean_ctor_get(v_s_3359_, 2);
v_enabled_3361_ = lean_ctor_get_uint8(v_s_3359_, sizeof(void*)*3);
v_assignment_3362_ = lean_ctor_get(v_s_3359_, 0);
v_lazyAssignment_3363_ = lean_ctor_get(v_s_3359_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_s_3359_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3365_ = v_s_3359_;
v_isShared_3366_ = v_isSharedCheck_3383_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_trees_3360_);
lean_inc(v_lazyAssignment_3363_);
lean_inc(v_assignment_3362_);
lean_dec(v_s_3359_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3383_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_size_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_size_3367_ = lean_ctor_get(v_trees_3360_, 2);
v___x_3368_ = lean_unsigned_to_nat(0u);
v___x_3369_ = lean_nat_dec_lt(v___x_3368_, v_size_3367_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3371_; 
lean_dec_ref(v_trees_3360_);
lean_dec(v_mvarId_3358_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 2, v_treesSaved_3357_);
v___x_3371_ = v___x_3365_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_assignment_3362_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_lazyAssignment_3363_);
lean_ctor_set(v_reuseFailAlloc_3372_, 2, v_treesSaved_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3372_, sizeof(void*)*3, v_enabled_3361_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3373_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__0));
v___x_3374_ = ((lean_object*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___redArg___closed__1));
v___x_3375_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3376_ = lean_unsigned_to_nat(1u);
v___x_3377_ = lean_nat_sub(v_size_3367_, v___x_3376_);
v___x_3378_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3375_, v_trees_3360_, v___x_3377_);
lean_dec(v___x_3377_);
lean_dec_ref(v_trees_3360_);
v___x_3379_ = l_Lean_PersistentHashMap_insert___redArg(v___x_3373_, v___x_3374_, v_assignment_3362_, v_mvarId_3358_, v___x_3378_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 2, v_treesSaved_3357_);
lean_ctor_set(v___x_3365_, 0, v___x_3379_);
v___x_3381_ = v___x_3365_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_lazyAssignment_3363_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_treesSaved_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3382_, sizeof(void*)*3, v_enabled_3361_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0(lean_object* v_modifyInfoState_3384_, lean_object* v___f_3385_, lean_object* v_x_3386_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_apply_1(v_modifyInfoState_3384_, v___f_3385_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__0___boxed(lean_object* v_modifyInfoState_3388_, lean_object* v___f_3389_, lean_object* v_x_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_Elab_withInfoHole___redArg___lam__0(v_modifyInfoState_3388_, v___f_3389_, v_x_3390_);
lean_dec(v_x_3390_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg___lam__2(lean_object* v_toApplicative_3392_, lean_object* v_mvarId_3393_, lean_object* v_modifyInfoState_3394_, lean_object* v_inst_3395_, lean_object* v_x_3396_, lean_object* v___f_3397_, lean_object* v_treesSaved_3398_){
_start:
{
lean_object* v_toFunctor_3399_; lean_object* v_map_3400_; lean_object* v___f_3401_; lean_object* v___f_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_toFunctor_3399_ = lean_ctor_get(v_toApplicative_3392_, 0);
lean_inc_ref(v_toFunctor_3399_);
lean_dec_ref(v_toApplicative_3392_);
v_map_3400_ = lean_ctor_get(v_toFunctor_3399_, 0);
lean_inc(v_map_3400_);
lean_dec_ref(v_toFunctor_3399_);
v___f_3401_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3401_, 0, v_treesSaved_3398_);
lean_closure_set(v___f_3401_, 1, v_mvarId_3393_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3402_, 0, v_modifyInfoState_3394_);
lean_closure_set(v___f_3402_, 1, v___f_3401_);
v___x_3403_ = lean_apply_4(v_inst_3395_, lean_box(0), lean_box(0), v_x_3396_, v___f_3402_);
v___x_3404_ = lean_apply_4(v_map_3400_, lean_box(0), lean_box(0), v___f_3397_, v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole___redArg(lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_mvarId_3408_, lean_object* v_x_3409_){
_start:
{
lean_object* v_toApplicative_3410_; lean_object* v_toBind_3411_; lean_object* v_getInfoState_3412_; lean_object* v_modifyInfoState_3413_; lean_object* v___f_3414_; lean_object* v___f_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; 
v_toApplicative_3410_ = lean_ctor_get(v_inst_3406_, 0);
v_toBind_3411_ = lean_ctor_get(v_inst_3406_, 1);
lean_inc_n(v_toBind_3411_, 2);
v_getInfoState_3412_ = lean_ctor_get(v_inst_3407_, 0);
lean_inc(v_getInfoState_3412_);
v_modifyInfoState_3413_ = lean_ctor_get(v_inst_3407_, 1);
v___f_3414_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3409_);
lean_inc(v_modifyInfoState_3413_);
lean_inc_ref(v_toApplicative_3410_);
v___f_3415_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3415_, 0, v_toApplicative_3410_);
lean_closure_set(v___f_3415_, 1, v_mvarId_3408_);
lean_closure_set(v___f_3415_, 2, v_modifyInfoState_3413_);
lean_closure_set(v___f_3415_, 3, v_inst_3405_);
lean_closure_set(v___f_3415_, 4, v_x_3409_);
lean_closure_set(v___f_3415_, 5, v___f_3414_);
v___f_3416_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3416_, 0, v_x_3409_);
lean_closure_set(v___f_3416_, 1, v_inst_3406_);
lean_closure_set(v___f_3416_, 2, v_inst_3407_);
lean_closure_set(v___f_3416_, 3, v_toBind_3411_);
lean_closure_set(v___f_3416_, 4, v___f_3415_);
v___x_3417_ = lean_apply_4(v_toBind_3411_, lean_box(0), lean_box(0), v_getInfoState_3412_, v___f_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoHole(lean_object* v_m_3418_, lean_object* v_00_u03b1_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_mvarId_3423_, lean_object* v_x_3424_){
_start:
{
lean_object* v_toApplicative_3425_; lean_object* v_toBind_3426_; lean_object* v_getInfoState_3427_; lean_object* v_modifyInfoState_3428_; lean_object* v___f_3429_; lean_object* v___f_3430_; lean_object* v___f_3431_; lean_object* v___x_3432_; 
v_toApplicative_3425_ = lean_ctor_get(v_inst_3421_, 0);
v_toBind_3426_ = lean_ctor_get(v_inst_3421_, 1);
lean_inc_n(v_toBind_3426_, 2);
v_getInfoState_3427_ = lean_ctor_get(v_inst_3422_, 0);
lean_inc(v_getInfoState_3427_);
v_modifyInfoState_3428_ = lean_ctor_get(v_inst_3422_, 1);
v___f_3429_ = ((lean_object*)(l_Lean_Elab_withInfoContext_x27___redArg___closed__0));
lean_inc(v_x_3424_);
lean_inc(v_modifyInfoState_3428_);
lean_inc_ref(v_toApplicative_3425_);
v___f_3430_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___redArg___lam__2), 7, 6);
lean_closure_set(v___f_3430_, 0, v_toApplicative_3425_);
lean_closure_set(v___f_3430_, 1, v_mvarId_3423_);
lean_closure_set(v___f_3430_, 2, v_modifyInfoState_3428_);
lean_closure_set(v___f_3430_, 3, v_inst_3420_);
lean_closure_set(v___f_3430_, 4, v_x_3424_);
lean_closure_set(v___f_3430_, 5, v___f_3429_);
v___f_3431_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_3431_, 0, v_x_3424_);
lean_closure_set(v___f_3431_, 1, v_inst_3421_);
lean_closure_set(v___f_3431_, 2, v_inst_3422_);
lean_closure_set(v___f_3431_, 3, v_toBind_3426_);
lean_closure_set(v___f_3431_, 4, v___f_3430_);
v___x_3432_ = lean_apply_4(v_toBind_3426_, lean_box(0), lean_box(0), v_getInfoState_3427_, v___f_3431_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0(uint8_t v_flag_3433_, lean_object* v_s_3434_){
_start:
{
lean_object* v_assignment_3435_; lean_object* v_lazyAssignment_3436_; lean_object* v_trees_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
v_assignment_3435_ = lean_ctor_get(v_s_3434_, 0);
v_lazyAssignment_3436_ = lean_ctor_get(v_s_3434_, 1);
v_trees_3437_ = lean_ctor_get(v_s_3434_, 2);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_s_3434_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v_s_3434_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_trees_3437_);
lean_inc(v_lazyAssignment_3436_);
lean_inc(v_assignment_3435_);
lean_dec(v_s_3434_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_assignment_3435_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_lazyAssignment_3436_);
lean_ctor_set(v_reuseFailAlloc_3443_, 2, v_trees_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*3, v_flag_3433_);
return v___x_3442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed(lean_object* v_flag_3445_, lean_object* v_s_3446_){
_start:
{
uint8_t v_flag_boxed_3447_; lean_object* v_res_3448_; 
v_flag_boxed_3447_ = lean_unbox(v_flag_3445_);
v_res_3448_ = l_Lean_Elab_enableInfoTree___redArg___lam__0(v_flag_boxed_3447_, v_s_3446_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg(lean_object* v_inst_3449_, uint8_t v_flag_3450_){
_start:
{
lean_object* v_modifyInfoState_3451_; lean_object* v___x_3452_; lean_object* v___f_3453_; lean_object* v___x_3454_; 
v_modifyInfoState_3451_ = lean_ctor_get(v_inst_3449_, 1);
lean_inc(v_modifyInfoState_3451_);
lean_dec_ref(v_inst_3449_);
v___x_3452_ = lean_box(v_flag_3450_);
v___f_3453_ = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3453_, 0, v___x_3452_);
v___x_3454_ = lean_apply_1(v_modifyInfoState_3451_, v___f_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___redArg___boxed(lean_object* v_inst_3455_, lean_object* v_flag_3456_){
_start:
{
uint8_t v_flag_boxed_3457_; lean_object* v_res_3458_; 
v_flag_boxed_3457_ = lean_unbox(v_flag_3456_);
v_res_3458_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3455_, v_flag_boxed_3457_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree(lean_object* v_m_3459_, lean_object* v_inst_3460_, uint8_t v_flag_3461_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3460_, v_flag_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___boxed(lean_object* v_m_3463_, lean_object* v_inst_3464_, lean_object* v_flag_3465_){
_start:
{
uint8_t v_flag_boxed_3466_; lean_object* v_res_3467_; 
v_flag_boxed_3466_ = lean_unbox(v_flag_3465_);
v_res_3467_ = l_Lean_Elab_enableInfoTree(v_m_3463_, v_inst_3464_, v_flag_boxed_3466_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0(lean_object* v_x_3468_){
_start:
{
lean_object* v_fst_3469_; 
v_fst_3469_ = lean_ctor_get(v_x_3468_, 0);
lean_inc(v_fst_3469_);
return v_fst_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__0___boxed(lean_object* v_x_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__0(v_x_3470_);
lean_dec_ref(v_x_3470_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1(lean_object* v_x_3472_, lean_object* v_____r_3473_){
_start:
{
lean_inc(v_x_3472_);
return v_x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed(lean_object* v_x_3474_, lean_object* v_____r_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__1(v_x_3474_, v_____r_3475_);
lean_dec(v_x_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2(lean_object* v___x_3477_, lean_object* v_x_3478_){
_start:
{
lean_inc(v___x_3477_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed(lean_object* v___x_3479_, lean_object* v_x_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__2(v___x_3479_, v_x_3480_);
lean_dec(v_x_3480_);
lean_dec(v___x_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3(lean_object* v_toFunctor_3482_, lean_object* v_inst_3483_, uint8_t v_flag_3484_, lean_object* v_toBind_3485_, lean_object* v___f_3486_, lean_object* v_inst_3487_, lean_object* v___f_3488_, lean_object* v_____do__lift_3489_){
_start:
{
uint8_t v_enabled_3490_; lean_object* v_map_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___f_3495_; lean_object* v_y_3496_; lean_object* v___x_3497_; 
v_enabled_3490_ = lean_ctor_get_uint8(v_____do__lift_3489_, sizeof(void*)*3);
v_map_3491_ = lean_ctor_get(v_toFunctor_3482_, 0);
lean_inc(v_map_3491_);
lean_dec_ref(v_toFunctor_3482_);
lean_inc_ref(v_inst_3483_);
v___x_3492_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3483_, v_flag_3484_);
v___x_3493_ = lean_apply_4(v_toBind_3485_, lean_box(0), lean_box(0), v___x_3492_, v___f_3486_);
v___x_3494_ = l_Lean_Elab_enableInfoTree___redArg(v_inst_3483_, v_enabled_3490_);
v___f_3495_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_3495_, 0, v___x_3494_);
v_y_3496_ = lean_apply_4(v_inst_3487_, lean_box(0), lean_box(0), v___x_3493_, v___f_3495_);
v___x_3497_ = lean_apply_4(v_map_3491_, lean_box(0), lean_box(0), v___f_3488_, v_y_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed(lean_object* v_toFunctor_3498_, lean_object* v_inst_3499_, lean_object* v_flag_3500_, lean_object* v_toBind_3501_, lean_object* v___f_3502_, lean_object* v_inst_3503_, lean_object* v___f_3504_, lean_object* v_____do__lift_3505_){
_start:
{
uint8_t v_flag_boxed_3506_; lean_object* v_res_3507_; 
v_flag_boxed_3506_ = lean_unbox(v_flag_3500_);
v_res_3507_ = l_Lean_Elab_withEnableInfoTree___redArg___lam__3(v_toFunctor_3498_, v_inst_3499_, v_flag_boxed_3506_, v_toBind_3501_, v___f_3502_, v_inst_3503_, v___f_3504_, v_____do__lift_3505_);
lean_dec_ref(v_____do__lift_3505_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg(lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, uint8_t v_flag_3512_, lean_object* v_x_3513_){
_start:
{
lean_object* v_toApplicative_3514_; lean_object* v_toBind_3515_; lean_object* v_getInfoState_3516_; lean_object* v_toFunctor_3517_; lean_object* v___f_3518_; lean_object* v___f_3519_; lean_object* v___x_3520_; lean_object* v___f_3521_; lean_object* v___x_3522_; 
v_toApplicative_3514_ = lean_ctor_get(v_inst_3509_, 0);
lean_inc_ref(v_toApplicative_3514_);
v_toBind_3515_ = lean_ctor_get(v_inst_3509_, 1);
lean_inc_n(v_toBind_3515_, 2);
lean_dec_ref(v_inst_3509_);
v_getInfoState_3516_ = lean_ctor_get(v_inst_3510_, 0);
lean_inc(v_getInfoState_3516_);
v_toFunctor_3517_ = lean_ctor_get(v_toApplicative_3514_, 0);
lean_inc_ref(v_toFunctor_3517_);
lean_dec_ref(v_toApplicative_3514_);
v___f_3518_ = ((lean_object*)(l_Lean_Elab_withEnableInfoTree___redArg___closed__0));
v___f_3519_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3519_, 0, v_x_3513_);
v___x_3520_ = lean_box(v_flag_3512_);
v___f_3521_ = lean_alloc_closure((void*)(l_Lean_Elab_withEnableInfoTree___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_3521_, 0, v_toFunctor_3517_);
lean_closure_set(v___f_3521_, 1, v_inst_3510_);
lean_closure_set(v___f_3521_, 2, v___x_3520_);
lean_closure_set(v___f_3521_, 3, v_toBind_3515_);
lean_closure_set(v___f_3521_, 4, v___f_3519_);
lean_closure_set(v___f_3521_, 5, v_inst_3511_);
lean_closure_set(v___f_3521_, 6, v___f_3518_);
v___x_3522_ = lean_apply_4(v_toBind_3515_, lean_box(0), lean_box(0), v_getInfoState_3516_, v___f_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___redArg___boxed(lean_object* v_inst_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_flag_3526_, lean_object* v_x_3527_){
_start:
{
uint8_t v_flag_boxed_3528_; lean_object* v_res_3529_; 
v_flag_boxed_3528_ = lean_unbox(v_flag_3526_);
v_res_3529_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3523_, v_inst_3524_, v_inst_3525_, v_flag_boxed_3528_, v_x_3527_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree(lean_object* v_m_3530_, lean_object* v_00_u03b1_3531_, lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_inst_3534_, uint8_t v_flag_3535_, lean_object* v_x_3536_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_Elab_withEnableInfoTree___redArg(v_inst_3532_, v_inst_3533_, v_inst_3534_, v_flag_3535_, v_x_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___boxed(lean_object* v_m_3538_, lean_object* v_00_u03b1_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, lean_object* v_flag_3543_, lean_object* v_x_3544_){
_start:
{
uint8_t v_flag_boxed_3545_; lean_object* v_res_3546_; 
v_flag_boxed_3545_ = lean_unbox(v_flag_3543_);
v_res_3546_ = l_Lean_Elab_withEnableInfoTree(v_m_3538_, v_00_u03b1_3539_, v_inst_3540_, v_inst_3541_, v_inst_3542_, v_flag_boxed_3545_, v_x_3544_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg___lam__0(lean_object* v_toPure_3547_, lean_object* v_____do__lift_3548_){
_start:
{
lean_object* v_trees_3549_; lean_object* v___x_3550_; 
v_trees_3549_ = lean_ctor_get(v_____do__lift_3548_, 2);
lean_inc_ref(v_trees_3549_);
lean_dec_ref(v_____do__lift_3548_);
v___x_3550_ = lean_apply_2(v_toPure_3547_, lean_box(0), v_trees_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___redArg(lean_object* v_inst_3551_, lean_object* v_inst_3552_){
_start:
{
lean_object* v_toApplicative_3553_; lean_object* v_toBind_3554_; lean_object* v_getInfoState_3555_; lean_object* v_toPure_3556_; lean_object* v___f_3557_; lean_object* v___x_3558_; 
v_toApplicative_3553_ = lean_ctor_get(v_inst_3552_, 0);
lean_inc_ref(v_toApplicative_3553_);
v_toBind_3554_ = lean_ctor_get(v_inst_3552_, 1);
lean_inc(v_toBind_3554_);
lean_dec_ref(v_inst_3552_);
v_getInfoState_3555_ = lean_ctor_get(v_inst_3551_, 0);
lean_inc(v_getInfoState_3555_);
lean_dec_ref(v_inst_3551_);
v_toPure_3556_ = lean_ctor_get(v_toApplicative_3553_, 1);
lean_inc(v_toPure_3556_);
lean_dec_ref(v_toApplicative_3553_);
v___f_3557_ = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3557_, 0, v_toPure_3556_);
v___x_3558_ = lean_apply_4(v_toBind_3554_, lean_box(0), lean_box(0), v_getInfoState_3555_, v___f_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees(lean_object* v_m_3559_, lean_object* v_inst_3560_, lean_object* v_inst_3561_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Lean_Elab_getInfoTrees___redArg(v_inst_3560_, v_inst_3561_);
return v___x_3562_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_InfoTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_InfoTree_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_InfoTree_Main(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Elab.Command
// Imports: Lean.Elab.Alias Lean.Elab.Log Lean.Elab.ResolveName Lean.Elab.Term Lean.Elab.Binders Lean.Elab.SyntheticMVars
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
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSection(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_Command_8__updateState___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__3;
lean_object* l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(lean_object*);
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_check___closed__1;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Lean_Elab_Command_getOptions(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_4__modifyGetState(lean_object*);
lean_object* l_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__3;
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Command_withNamespace(lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_12__addScopes(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_5__elabCommandUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_mkHashMap___at_Lean_Elab_Command_commandElabAttribute___spec__2(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1;
lean_object* l___private_Lean_Elab_Command_7__mkTermState___boxed(lean_object*);
uint8_t l_Lean_Name_lt___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIOCore(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1;
lean_object* l_Lean_Elab_Command_elabEval___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_registerTraceClass___closed__1;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO(lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
uint8_t l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withNamespace___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_15__checkEndHeader___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withIncRecDepth___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_verboseOption___closed__3;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter;
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2;
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__4;
lean_object* l___private_Lean_Elab_Command_11__addScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_Command_elabCheck(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1;
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_init__quot___elambda__1___closed__2;
extern lean_object* l_Lean_getMaxRecDepth___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__11;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__2;
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_add_alias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_4__modifyGetState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Exception_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_Scope_inhabited;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1;
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_12__addScopes___main___closed__3;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption___closed__3;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
extern lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__3;
lean_object* l_Lean_Elab_Command_elabSynth___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__9;
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabCheckFailure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__9;
lean_object* l_Lean_Elab_Command_State_inhabited___closed__3;
lean_object* l___private_Lean_Elab_Command_14__checkAnonymousScope___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___closed__3;
lean_object* l_Lean_Elab_Command_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Command_15__checkEndHeader(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_12__addScopes___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1;
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3;
lean_object* l_Lean_Elab_Term_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* lean_with_isolated_streams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__1;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___closed__2;
lean_object* l___private_Lean_Elab_Command_10__toCommandResult___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_Elab_Command_elabSynth(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_9__getVarDecls___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_run___rarg___closed__5;
lean_object* l___private_Lean_Elab_Command_12__addScopes___main___closed__2;
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_Lean_Elab_Command_setOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2;
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_5__elabCommandUsing___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__9;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__10;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withoutModifyingEnv___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_1__ioErrorToMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_Monad;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___closed__1;
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__3;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__2;
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__3;
lean_object* l_Lean_Elab_Command_dbgTrace(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4;
lean_object* l_Lean_Elab_Command_elabEnd___closed__8;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__8;
extern lean_object* l_Lean_choiceKind___closed__2;
extern lean_object* l_Lean_Expr_isSyntheticSorry___closed__1;
lean_object* l_Lean_Elab_Command_elabCheck___closed__2;
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_Command_set__option___elambda__1___closed__2;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__7;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Command_withoutModifyingEnv(lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__3;
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*);
extern lean_object* l_Lean_Parser_Command_docComment___elambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__4;
lean_object* l___private_Lean_Elab_Command_10__toCommandResult___rarg___closed__1;
extern lean_object* l_Lean_Parser_Command_eval___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_10__toCommandResult___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEval___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclId___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__6;
lean_object* l_Lean_Elab_Command_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__6;
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState;
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l___private_Lean_Elab_Command_13__addNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2;
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_1__ioErrorToMessage(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Elab_Command_elabCommand___main___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Command_15__checkEndHeader___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3;
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Exception_hasToString___closed__1;
lean_object* l___private_Lean_Elab_Command_12__addScopes___main___closed__1;
extern lean_object* l_PersistentArray_empty___closed__3;
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport(lean_object*);
lean_object* l_Lean_Elab_Command_getScopes(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elbChoice(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_docComment___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabExport(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__5;
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_hasNoErrorMessages(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withLogging(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
uint8_t l_Array_contains___at_Lean_findField_x3f___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__2;
lean_object* l_Lean_Elab_Command_elabSetOption___closed__1;
lean_object* l_Lean_Elab_Command_Scope_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabSetOption___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection___closed__1;
lean_object* l_Lean_Elab_Command_liftIOCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Command_elabEnd(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerAttributeImplBuilder___closed__2;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___closed__3;
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4;
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabChoiceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__4;
lean_object* l___private_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd(lean_object*);
lean_object* l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__4;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Lean_Elab_Command_6__mkTermContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog;
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4;
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___closed__2;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__1;
lean_object* l_Lean_Elab_Command_failIfSucceeds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand___main___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Elab_Command_elabCommand___main___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__1;
lean_object* l___private_Lean_Elab_Command_15__checkEndHeader___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_Command_getScope(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_7__mkTermState(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__6;
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_check__failure___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__7;
lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabEval(lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_Elab_Command_State_inhabited___closed__2;
lean_object* l_Lean_Elab_Command_withDeclId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__5;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withIncRecDepth(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__3;
extern lean_object* l_Lean_EnvExtension_setState___closed__1;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__2;
lean_object* l_Lean_Elab_Command_elbChoice___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen(lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___closed__2;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_compileDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__4;
lean_object* l___private_Lean_Elab_Command_8__updateState(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__8;
extern lean_object* l_Lean_Parser_Command_eval___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__4;
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited;
uint8_t l___private_Lean_Elab_Command_14__checkAnonymousScope(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getOpenDecls(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Command_trace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Parser_Command_export___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Command_9__getVarDecls(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_getEnv(lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_object*);
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___closed__3;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_10__toCommandResult(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__3;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1;
extern lean_object* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___closed__3;
lean_object* l___private_Lean_Elab_Command_12__addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth(lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7;
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__9;
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setEnv(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_withDeclId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_variables___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__3;
lean_object* l_Lean_Elab_Command_liftIOCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval(lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__10;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Command_elabChoiceAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__8;
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables(lean_object*);
uint8_t l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__5;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabChoiceAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_Elab_mkMacroAttribute___closed__2;
lean_object* l___private_Lean_Elab_Command_13__addNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
lean_object* l_Lean_Elab_Command_elabEnd___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__5;
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_synth___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___closed__3;
lean_object* l_Lean_Elab_Command_elabChoiceAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Command_12__addScopes___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__5;
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__3;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Lean_Elab_Command_logTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_regBuiltinCommandParserAttr___closed__3;
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__11;
lean_object* l_Lean_Elab_Command_throwError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l_Lean_Elab_Command_Exception_inhabited;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Command_Scope_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Options_empty;
x_4 = lean_box(0);
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set(x_6, 5, x_1);
lean_ctor_set(x_6, 6, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_Scope_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Scope_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("root");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_inhabited___closed__1;
x_3 = l_String_splitAux___main___closed__1;
x_4 = l_Lean_Options_empty;
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
x_7 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_1);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set(x_7, 6, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_inhabited___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtension_setState___closed__1;
x_2 = l_PersistentArray_empty___closed__3;
x_3 = l_Lean_Elab_Command_State_inhabited___closed__3;
x_4 = l_Lean_Unhygienic_run___rarg___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_inhabited___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_mkState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_box(0);
x_5 = l_Lean_Elab_Command_State_inhabited___closed__1;
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean_box(0);
x_8 = l_Array_empty___closed__1;
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_4);
lean_ctor_set(x_9, 6, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = l_Lean_getMaxRecDepth(x_3);
lean_dec(x_3);
x_12 = l_Lean_Unhygienic_run___rarg___closed__1;
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_11);
return x_13;
}
}
lean_object* _init_l_Lean_Elab_Command_Exception_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Exception_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_8);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_10);
lean_dec(x_6);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Elab_Command_mkMessageAux(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Command_1__ioErrorToMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_Lean_Elab_getBetterRef(x_2, x_4);
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_addMacroStack(x_8, x_4);
x_10 = 2;
x_11 = l_Lean_Elab_Command_mkMessageAux(x_1, x_5, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Command_1__ioErrorToMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_liftIOCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_2, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_2, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Command_liftIOCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftIOCore___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftIOCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftIOCore___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_3, x_1, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_3, x_1, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Command_liftIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftIO___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftIO___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Command_2__getState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_io_ref_get(x_3, x_2);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_box(0);
x_12 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_16, x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_3__setState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_io_ref_set(x_4, x_1, x_3);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_2, x_12, x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_2, x_17, x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_4__modifyGetState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lean_Elab_Command_3__setState(x_9, x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_4__modifyGetState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_4__modifyGetState___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_2__getState), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_3__setState), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_4__modifyGetState), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2;
x_3 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_2__getState(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_Scope_inhabited;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Lean_Elab_Command_getScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_2__getState(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Command_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Command_getOptions(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_MetavarContext_Inhabited___closed__1;
x_11 = l_Lean_LocalContext_Inhabited___closed__2;
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = l_Lean_MetavarContext_Inhabited___closed__1;
x_17 = l_Lean_LocalContext_Inhabited___closed__2;
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_14);
x_19 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_PersistentArray_push___rarg(x_8, x_1);
lean_ctor_set(x_5, 1, x_9);
x_10 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get(x_5, 3);
x_25 = lean_ctor_get(x_5, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_26 = l_PersistentArray_push___rarg(x_22, x_1);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_25);
x_28 = l___private_Lean_Elab_Command_3__setState(x_27, x_2, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
return x_4;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_addContext), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
x_3 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__9;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__11;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_addContext(x_1, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = l_String_splitAux___main___closed__1;
x_15 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_2);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = l_String_splitAux___main___closed__1;
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lean_FileMap_toPosition(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_Elab_Command_addContext(x_1, x_4, x_5);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_box(0);
x_34 = l_String_splitAux___main___closed__1;
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_2);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = l_String_splitAux___main___closed__1;
x_40 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_29);
lean_dec(x_26);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(x_1, x_2, x_9, x_4, x_8);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 5);
lean_inc(x_5);
lean_inc(x_5);
x_6 = l_Lean_Elab_getBetterRef(x_1, x_5);
x_7 = l_Lean_Elab_addMacroStack(x_2, x_5);
x_8 = 2;
x_9 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(x_7, x_8, x_6, x_3, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Command_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwError___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_throwError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_throwError___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
lean_inc(x_4);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(x_3, x_2, x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
x_10 = l___private_Lean_Elab_Command_2__getState(x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_PersistentArray_push___rarg(x_14, x_8);
lean_ctor_set(x_11, 1, x_15);
x_16 = l___private_Lean_Elab_Command_3__setState(x_11, x_4, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
x_30 = lean_ctor_get(x_11, 3);
x_31 = lean_ctor_get(x_11, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_32 = l_PersistentArray_push___rarg(x_28, x_8);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
x_34 = l___private_Lean_Elab_Command_3__setState(x_33, x_4, x_12);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_10);
if (x_43 == 0)
{
return x_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_7);
if (x_47 == 0)
{
return x_7;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_7, 0);
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_7);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_logTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_inc(x_4);
x_7 = l_Lean_Elab_Command_addContext(x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 0;
x_11 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_2, x_10, x_8, x_4, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_logTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_logTrace(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_trace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Command_getOptions(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_10 = l_Lean_checkTraceOption(x_8, x_1);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_6);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_3, x_12);
x_14 = l_Lean_Elab_Command_logTrace(x_1, x_2, x_13, x_4, x_9);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
lean_inc(x_1);
x_17 = l_Lean_checkTraceOption(x_15, x_1);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_box(0);
x_21 = lean_apply_1(x_3, x_20);
x_22 = l_Lean_Elab_Command_logTrace(x_1, x_2, x_21, x_4, x_16);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_Command_trace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_trace(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwUnsupportedSyntax___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_throwUnsupportedSyntax(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getCurrMacroScope(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getMainModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getEnv(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_environment_main_module(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_environment_main_module(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_ctor_set(x_5, 3, x_10);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 6);
lean_dec(x_14);
lean_ctor_set(x_2, 6, x_8);
x_15 = lean_apply_2(x_1, x_2, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
x_20 = lean_ctor_get(x_2, 4);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_22, 6, x_8);
x_23 = lean_apply_2(x_1, x_22, x_12);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_31, x_33);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_32);
lean_inc(x_2);
x_36 = l___private_Lean_Elab_Command_3__setState(x_35, x_2, x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 5);
lean_inc(x_43);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_44 = x_2;
} else {
 lean_dec_ref(x_2);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 7, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set(x_45, 5, x_43);
lean_ctor_set(x_45, 6, x_31);
x_46 = lean_apply_2(x_1, x_45, x_37);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_4);
if (x_51 == 0)
{
return x_4;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_4, 0);
x_53 = lean_ctor_get(x_4, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_4);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getCurrMacroScope___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getMainModule), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2;
x_3 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkMacroAttribute___closed__2;
x_2 = l_Lean_Parser_Command_docComment___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElabAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__1;
x_2 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinCommandElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CommandElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__1;
x_2 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__3;
x_3 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__5;
x_4 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__7;
x_5 = l_Lean_Parser_Command_docComment___elambda__1___closed__2;
x_6 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__9;
x_7 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__3;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_mkHashMap___at_Lean_Elab_Command_commandElabAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_commandElabAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Elab_Command_commandElabAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Command_commandElabAttribute___closed__3;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_commandElabAttribute___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_nat_dec_eq(x_11, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_3, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_3, 0);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_11, x_25);
lean_dec(x_11);
lean_ctor_set(x_3, 3, x_26);
x_27 = lean_apply_2(x_2, x_3, x_7);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_11, x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_10);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_12);
lean_ctor_set(x_30, 5, x_13);
lean_ctor_set(x_30, 6, x_14);
x_31 = lean_apply_2(x_2, x_30, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_32 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_33 = l_Lean_Elab_Command_throwError___rarg(x_1, x_32, x_3, x_7);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
return x_5;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Lean_Elab_Command_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withIncRecDepth___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withIncRecDepth___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_withIncRecDepth___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Command_5__elabCommandUsing___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Lean_Syntax_prettyPrint(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofList___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Command_throwError___rarg(x_2, x_13, x_4, x_5);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_17 = lean_apply_3(x_15, x_2, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l___private_Lean_Elab_Command_3__setState(x_1, x_4, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_3 = x_16;
x_5 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Command_5__elabCommandUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Command_5__elabCommandUsing___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_4, 5, x_9);
x_10 = lean_apply_2(x_3, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_20 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set(x_20, 6, x_17);
x_21 = lean_apply_2(x_3, x_20, x_5);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withMacroExpansion___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 3);
lean_dec(x_8);
lean_ctor_set(x_5, 3, x_1);
x_9 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 2);
x_23 = lean_ctor_get(x_5, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_1);
lean_ctor_set(x_24, 4, x_23);
x_25 = l___private_Lean_Elab_Command_3__setState(x_24, x_2, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_4);
if (x_34 == 0)
{
return x_4;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_4, 0);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1;
x_2 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getEnv), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__2), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwError), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwUnsupportedSyntax___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3;
x_2 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
x_3 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2;
x_4 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4;
x_5 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5;
x_6 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Elab_Command_elabCommand___main___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find_x3f___main___at_Lean_Elab_Command_elabCommand___main___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
lean_inc(x_3);
x_12 = l_Lean_Elab_Command_elabCommand___main(x_9, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabCommand___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabCommand___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_nat_dec_eq(x_10, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_2, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_10, x_24);
lean_dec(x_10);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_ctor_set(x_2, 3, x_25);
lean_inc(x_2);
x_26 = l___private_Lean_Elab_Command_2__getState(x_2, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 3);
x_31 = lean_nat_add(x_30, x_24);
lean_ctor_set(x_27, 3, x_31);
x_32 = l___private_Lean_Elab_Command_3__setState(x_27, x_2, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_30);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_9);
lean_ctor_set(x_34, 3, x_25);
lean_ctor_set(x_34, 4, x_11);
lean_ctor_set(x_34, 5, x_12);
lean_ctor_set(x_34, 6, x_30);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = l_Lean_nullKind;
x_38 = lean_name_eq(x_35, x_37);
lean_dec(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_153; 
lean_dec(x_36);
lean_inc(x_34);
x_153 = l_Lean_Elab_Command_getOptions(x_34, x_33);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Elab_Command_elabCommand___main___closed__1;
x_157 = l_Lean_checkTraceOption(x_154, x_156);
lean_dec(x_154);
if (x_157 == 0)
{
x_39 = x_155;
goto block_152;
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_inc(x_1);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_1);
lean_inc(x_34);
x_159 = l_Lean_Elab_Command_logTrace(x_156, x_1, x_158, x_34, x_155);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_39 = x_160;
goto block_152;
}
else
{
uint8_t x_161; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_159);
if (x_161 == 0)
{
return x_159;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_159, 0);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_159);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_153);
if (x_165 == 0)
{
return x_153;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_153, 0);
x_167 = lean_ctor_get(x_153, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_153);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
block_152:
{
lean_object* x_40; 
lean_inc(x_34);
x_40 = l___private_Lean_Elab_Command_2__getState(x_34, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_69 = l_Lean_Elab_Command_getCurrMacroScope(x_34, x_42);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_34);
x_72 = l_Lean_Elab_Command_getEnv(x_34, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_34);
x_75 = l___private_Lean_Elab_Command_2__getState(x_34, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 3);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_environment_main_module(x_73);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_70);
lean_inc(x_1);
x_81 = l_Lean_Elab_getMacros(x_43, x_1, x_80, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_34);
x_84 = l___private_Lean_Elab_Command_2__getState(x_34, x_77);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 3);
lean_dec(x_88);
lean_ctor_set(x_85, 3, x_83);
lean_inc(x_34);
x_89 = l___private_Lean_Elab_Command_3__setState(x_85, x_34, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_82);
x_44 = x_91;
x_45 = x_90;
goto block_68;
}
else
{
lean_object* x_92; 
lean_dec(x_82);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_89, 0);
lean_dec(x_94);
return x_89;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
lean_dec(x_89);
x_98 = lean_box(0);
x_44 = x_98;
x_45 = x_97;
goto block_68;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_85, 0);
x_100 = lean_ctor_get(x_85, 1);
x_101 = lean_ctor_get(x_85, 2);
x_102 = lean_ctor_get(x_85, 4);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_85);
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_101);
lean_ctor_set(x_103, 3, x_83);
lean_ctor_set(x_103, 4, x_102);
lean_inc(x_34);
x_104 = l___private_Lean_Elab_Command_3__setState(x_103, x_34, x_86);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_82);
x_44 = x_106;
x_45 = x_105;
goto block_68;
}
else
{
lean_object* x_107; 
lean_dec(x_82);
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_109 = x_104;
} else {
 lean_dec_ref(x_104);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_dec(x_104);
x_112 = lean_box(0);
x_44 = x_112;
x_45 = x_111;
goto block_68;
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_83);
lean_dec(x_82);
x_113 = lean_ctor_get(x_84, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_84);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_84, 0);
lean_dec(x_115);
return x_84;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_84, 1);
lean_inc(x_116);
lean_dec(x_84);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_84, 1);
lean_inc(x_118);
lean_dec(x_84);
x_119 = lean_box(0);
x_44 = x_119;
x_45 = x_118;
goto block_68;
}
}
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_81, 0);
lean_inc(x_120);
lean_dec(x_81);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
lean_inc(x_34);
x_125 = l_Lean_Elab_Command_throwError___rarg(x_121, x_124, x_34, x_77);
lean_dec(x_121);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_125);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_125, 0);
lean_dec(x_128);
return x_125;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_dec(x_125);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_dec(x_125);
x_132 = lean_box(0);
x_44 = x_132;
x_45 = x_131;
goto block_68;
}
}
else
{
lean_object* x_133; 
x_133 = lean_box(0);
x_44 = x_133;
x_45 = x_77;
goto block_68;
}
}
}
else
{
lean_object* x_134; 
lean_dec(x_73);
lean_dec(x_70);
x_134 = lean_ctor_get(x_75, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_75);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_75, 0);
lean_dec(x_136);
return x_75;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_75, 1);
lean_inc(x_137);
lean_dec(x_75);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_75, 1);
lean_inc(x_139);
lean_dec(x_75);
x_140 = lean_box(0);
x_44 = x_140;
x_45 = x_139;
goto block_68;
}
}
}
else
{
lean_object* x_141; 
lean_dec(x_70);
x_141 = lean_ctor_get(x_72, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_72);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_72, 0);
lean_dec(x_143);
return x_72;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_72, 1);
lean_inc(x_144);
lean_dec(x_72);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_72, 1);
lean_inc(x_146);
lean_dec(x_72);
x_147 = lean_box(0);
x_44 = x_147;
x_45 = x_146;
goto block_68;
}
}
block_68:
{
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_46 = l_Lean_Elab_Command_commandElabAttribute;
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = l_Lean_PersistentEnvExtension_getState___rarg(x_47, x_43);
lean_dec(x_43);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_1);
x_50 = l_Lean_Syntax_getKind(x_1);
x_51 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(x_49, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_50);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_Elab_Term_elabUsingElabFns___closed__3;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Elab_Term_elabUsingElabFns___closed__6;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Command_throwError___rarg(x_1, x_59, x_34, x_45);
lean_dec(x_1);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_50);
x_61 = lean_ctor_get(x_51, 0);
lean_inc(x_61);
lean_dec(x_51);
x_62 = l___private_Lean_Elab_Command_5__elabCommandUsing___main(x_41, x_1, x_61, x_34, x_45);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_34);
x_63 = lean_ctor_get(x_44, 0);
lean_inc(x_63);
lean_dec(x_44);
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_12);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_7);
lean_ctor_set(x_66, 1, x_8);
lean_ctor_set(x_66, 2, x_9);
lean_ctor_set(x_66, 3, x_25);
lean_ctor_set(x_66, 4, x_11);
lean_ctor_set(x_66, 5, x_65);
lean_ctor_set(x_66, 6, x_30);
x_1 = x_63;
x_2 = x_66;
x_3 = x_45;
goto _start;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_40);
if (x_148 == 0)
{
return x_40;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_40, 0);
x_150 = lean_ctor_get(x_40, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_40);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_169 = lean_unsigned_to_nat(0u);
x_170 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(x_36, x_169, x_34, x_33);
lean_dec(x_36);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_171 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_172 = l_Lean_Elab_Command_throwError___rarg(x_1, x_171, x_34, x_33);
lean_dec(x_1);
return x_172;
}
}
else
{
uint8_t x_173; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_32);
if (x_173 == 0)
{
return x_32;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_32, 0);
x_175 = lean_ctor_get(x_32, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_32);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_177 = lean_ctor_get(x_27, 0);
x_178 = lean_ctor_get(x_27, 1);
x_179 = lean_ctor_get(x_27, 2);
x_180 = lean_ctor_get(x_27, 3);
x_181 = lean_ctor_get(x_27, 4);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_27);
x_182 = lean_nat_add(x_180, x_24);
x_183 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_183, 0, x_177);
lean_ctor_set(x_183, 1, x_178);
lean_ctor_set(x_183, 2, x_179);
lean_ctor_set(x_183, 3, x_182);
lean_ctor_set(x_183, 4, x_181);
x_184 = l___private_Lean_Elab_Command_3__setState(x_183, x_2, x_28);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
lean_inc(x_180);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_186 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_186, 0, x_7);
lean_ctor_set(x_186, 1, x_8);
lean_ctor_set(x_186, 2, x_9);
lean_ctor_set(x_186, 3, x_25);
lean_ctor_set(x_186, 4, x_11);
lean_ctor_set(x_186, 5, x_12);
lean_ctor_set(x_186, 6, x_180);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_1, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_1, 1);
lean_inc(x_188);
x_189 = l_Lean_nullKind;
x_190 = lean_name_eq(x_187, x_189);
lean_dec(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_290; 
lean_dec(x_188);
lean_inc(x_186);
x_290 = l_Lean_Elab_Command_getOptions(x_186, x_185);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = l_Lean_Elab_Command_elabCommand___main___closed__1;
x_294 = l_Lean_checkTraceOption(x_291, x_293);
lean_dec(x_291);
if (x_294 == 0)
{
x_191 = x_292;
goto block_289;
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_inc(x_1);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_1);
lean_inc(x_186);
x_296 = l_Lean_Elab_Command_logTrace(x_293, x_1, x_295, x_186, x_292);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_191 = x_297;
goto block_289;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_296, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_300 = x_296;
} else {
 lean_dec_ref(x_296);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_302 = lean_ctor_get(x_290, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_290, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_304 = x_290;
} else {
 lean_dec_ref(x_290);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
block_289:
{
lean_object* x_192; 
lean_inc(x_186);
x_192 = l___private_Lean_Elab_Command_2__getState(x_186, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
x_221 = l_Lean_Elab_Command_getCurrMacroScope(x_186, x_194);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_inc(x_186);
x_224 = l_Lean_Elab_Command_getEnv(x_186, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
lean_inc(x_186);
x_227 = l___private_Lean_Elab_Command_2__getState(x_186, x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get(x_228, 3);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_environment_main_module(x_225);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_222);
lean_inc(x_1);
x_233 = l_Lean_Elab_getMacros(x_195, x_1, x_232, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
lean_inc(x_186);
x_236 = l___private_Lean_Elab_Command_2__getState(x_186, x_229);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_237, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_237, 4);
lean_inc(x_242);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 lean_ctor_release(x_237, 2);
 lean_ctor_release(x_237, 3);
 lean_ctor_release(x_237, 4);
 x_243 = x_237;
} else {
 lean_dec_ref(x_237);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_239);
lean_ctor_set(x_244, 1, x_240);
lean_ctor_set(x_244, 2, x_241);
lean_ctor_set(x_244, 3, x_235);
lean_ctor_set(x_244, 4, x_242);
lean_inc(x_186);
x_245 = l___private_Lean_Elab_Command_3__setState(x_244, x_186, x_238);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_234);
x_196 = x_247;
x_197 = x_246;
goto block_220;
}
else
{
lean_object* x_248; 
lean_dec(x_234);
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_250 = x_245;
} else {
 lean_dec_ref(x_245);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_245, 1);
lean_inc(x_252);
lean_dec(x_245);
x_253 = lean_box(0);
x_196 = x_253;
x_197 = x_252;
goto block_220;
}
}
}
else
{
lean_object* x_254; 
lean_dec(x_235);
lean_dec(x_234);
x_254 = lean_ctor_get(x_236, 0);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_255 = lean_ctor_get(x_236, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_256 = x_236;
} else {
 lean_dec_ref(x_236);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_236, 1);
lean_inc(x_258);
lean_dec(x_236);
x_259 = lean_box(0);
x_196 = x_259;
x_197 = x_258;
goto block_220;
}
}
}
else
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_233, 0);
lean_inc(x_260);
lean_dec(x_233);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_263, 0, x_262);
x_264 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_264, 0, x_263);
lean_inc(x_186);
x_265 = l_Lean_Elab_Command_throwError___rarg(x_261, x_264, x_186, x_229);
lean_dec(x_261);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_268 = x_265;
} else {
 lean_dec_ref(x_265);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_265, 1);
lean_inc(x_270);
lean_dec(x_265);
x_271 = lean_box(0);
x_196 = x_271;
x_197 = x_270;
goto block_220;
}
}
else
{
lean_object* x_272; 
x_272 = lean_box(0);
x_196 = x_272;
x_197 = x_229;
goto block_220;
}
}
}
else
{
lean_object* x_273; 
lean_dec(x_225);
lean_dec(x_222);
x_273 = lean_ctor_get(x_227, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_274 = lean_ctor_get(x_227, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_275 = x_227;
} else {
 lean_dec_ref(x_227);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_227, 1);
lean_inc(x_277);
lean_dec(x_227);
x_278 = lean_box(0);
x_196 = x_278;
x_197 = x_277;
goto block_220;
}
}
}
else
{
lean_object* x_279; 
lean_dec(x_222);
x_279 = lean_ctor_get(x_224, 0);
lean_inc(x_279);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_280 = lean_ctor_get(x_224, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_281 = x_224;
} else {
 lean_dec_ref(x_224);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_224, 1);
lean_inc(x_283);
lean_dec(x_224);
x_284 = lean_box(0);
x_196 = x_284;
x_197 = x_283;
goto block_220;
}
}
block_220:
{
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_198 = l_Lean_Elab_Command_commandElabAttribute;
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
x_200 = l_Lean_PersistentEnvExtension_getState___rarg(x_199, x_195);
lean_dec(x_195);
lean_dec(x_199);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
lean_inc(x_1);
x_202 = l_Lean_Syntax_getKind(x_1);
x_203 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(x_201, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_193);
x_204 = l_Lean_Name_toString___closed__1;
x_205 = l_Lean_Name_toStringWithSep___main(x_204, x_202);
x_206 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = l_Lean_Elab_Term_elabUsingElabFns___closed__3;
x_209 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = l_Lean_Elab_Term_elabUsingElabFns___closed__6;
x_211 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Lean_Elab_Command_throwError___rarg(x_1, x_211, x_186, x_197);
lean_dec(x_1);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_202);
x_213 = lean_ctor_get(x_203, 0);
lean_inc(x_213);
lean_dec(x_203);
x_214 = l___private_Lean_Elab_Command_5__elabCommandUsing___main(x_193, x_1, x_213, x_186, x_197);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_186);
x_215 = lean_ctor_get(x_196, 0);
lean_inc(x_215);
lean_dec(x_196);
lean_inc(x_215);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_1);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_12);
x_218 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_218, 0, x_7);
lean_ctor_set(x_218, 1, x_8);
lean_ctor_set(x_218, 2, x_9);
lean_ctor_set(x_218, 3, x_25);
lean_ctor_set(x_218, 4, x_11);
lean_ctor_set(x_218, 5, x_217);
lean_ctor_set(x_218, 6, x_180);
x_1 = x_215;
x_2 = x_218;
x_3 = x_197;
goto _start;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_285 = lean_ctor_get(x_192, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_192, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_287 = x_192;
} else {
 lean_dec_ref(x_192);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_306 = lean_unsigned_to_nat(0u);
x_307 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(x_188, x_306, x_186, x_185);
lean_dec(x_188);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_308 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_309 = l_Lean_Elab_Command_throwError___rarg(x_1, x_308, x_186, x_185);
lean_dec(x_1);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_310 = lean_ctor_get(x_184, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_184, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_312 = x_184;
} else {
 lean_dec_ref(x_184);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_2);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_26);
if (x_314 == 0)
{
return x_26;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_26, 0);
x_316 = lean_ctor_get(x_26, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_26);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_2);
x_318 = lean_unsigned_to_nat(1u);
x_319 = lean_nat_add(x_10, x_318);
lean_dec(x_10);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_319);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_320 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_320, 0, x_7);
lean_ctor_set(x_320, 1, x_8);
lean_ctor_set(x_320, 2, x_9);
lean_ctor_set(x_320, 3, x_319);
lean_ctor_set(x_320, 4, x_11);
lean_ctor_set(x_320, 5, x_12);
lean_ctor_set(x_320, 6, x_13);
lean_inc(x_320);
x_321 = l___private_Lean_Elab_Command_2__getState(x_320, x_6);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_ctor_get(x_322, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_322, 2);
lean_inc(x_326);
x_327 = lean_ctor_get(x_322, 3);
lean_inc(x_327);
x_328 = lean_ctor_get(x_322, 4);
lean_inc(x_328);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 lean_ctor_release(x_322, 3);
 lean_ctor_release(x_322, 4);
 x_329 = x_322;
} else {
 lean_dec_ref(x_322);
 x_329 = lean_box(0);
}
x_330 = lean_nat_add(x_327, x_318);
if (lean_is_scalar(x_329)) {
 x_331 = lean_alloc_ctor(0, 5, 0);
} else {
 x_331 = x_329;
}
lean_ctor_set(x_331, 0, x_324);
lean_ctor_set(x_331, 1, x_325);
lean_ctor_set(x_331, 2, x_326);
lean_ctor_set(x_331, 3, x_330);
lean_ctor_set(x_331, 4, x_328);
x_332 = l___private_Lean_Elab_Command_3__setState(x_331, x_320, x_323);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
lean_dec(x_332);
lean_inc(x_327);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_319);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_334 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_334, 0, x_7);
lean_ctor_set(x_334, 1, x_8);
lean_ctor_set(x_334, 2, x_9);
lean_ctor_set(x_334, 3, x_319);
lean_ctor_set(x_334, 4, x_11);
lean_ctor_set(x_334, 5, x_12);
lean_ctor_set(x_334, 6, x_327);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; 
x_335 = lean_ctor_get(x_1, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_1, 1);
lean_inc(x_336);
x_337 = l_Lean_nullKind;
x_338 = lean_name_eq(x_335, x_337);
lean_dec(x_335);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_438; 
lean_dec(x_336);
lean_inc(x_334);
x_438 = l_Lean_Elab_Command_getOptions(x_334, x_333);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = l_Lean_Elab_Command_elabCommand___main___closed__1;
x_442 = l_Lean_checkTraceOption(x_439, x_441);
lean_dec(x_439);
if (x_442 == 0)
{
x_339 = x_440;
goto block_437;
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_inc(x_1);
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_1);
lean_inc(x_334);
x_444 = l_Lean_Elab_Command_logTrace(x_441, x_1, x_443, x_334, x_440);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; 
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec(x_444);
x_339 = x_445;
goto block_437;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_334);
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_446 = lean_ctor_get(x_444, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_444, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_448 = x_444;
} else {
 lean_dec_ref(x_444);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_334);
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_450 = lean_ctor_get(x_438, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_438, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_452 = x_438;
} else {
 lean_dec_ref(x_438);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_451);
return x_453;
}
block_437:
{
lean_object* x_340; 
lean_inc(x_334);
x_340 = l___private_Lean_Elab_Command_2__getState(x_334, x_339);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_343);
x_369 = l_Lean_Elab_Command_getCurrMacroScope(x_334, x_342);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
lean_inc(x_334);
x_372 = l_Lean_Elab_Command_getEnv(x_334, x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
lean_inc(x_334);
x_375 = l___private_Lean_Elab_Command_2__getState(x_334, x_374);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_ctor_get(x_376, 3);
lean_inc(x_378);
lean_dec(x_376);
x_379 = lean_environment_main_module(x_373);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_370);
lean_inc(x_1);
x_381 = l_Lean_Elab_getMacros(x_343, x_1, x_380, x_378);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
lean_inc(x_334);
x_384 = l___private_Lean_Elab_Command_2__getState(x_334, x_377);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_ctor_get(x_385, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_385, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_385, 4);
lean_inc(x_390);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 lean_ctor_release(x_385, 2);
 lean_ctor_release(x_385, 3);
 lean_ctor_release(x_385, 4);
 x_391 = x_385;
} else {
 lean_dec_ref(x_385);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(0, 5, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_387);
lean_ctor_set(x_392, 1, x_388);
lean_ctor_set(x_392, 2, x_389);
lean_ctor_set(x_392, 3, x_383);
lean_ctor_set(x_392, 4, x_390);
lean_inc(x_334);
x_393 = l___private_Lean_Elab_Command_3__setState(x_392, x_334, x_386);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec(x_393);
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_382);
x_344 = x_395;
x_345 = x_394;
goto block_368;
}
else
{
lean_object* x_396; 
lean_dec(x_382);
x_396 = lean_ctor_get(x_393, 0);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_334);
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_397 = lean_ctor_get(x_393, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_398 = x_393;
} else {
 lean_dec_ref(x_393);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_393, 1);
lean_inc(x_400);
lean_dec(x_393);
x_401 = lean_box(0);
x_344 = x_401;
x_345 = x_400;
goto block_368;
}
}
}
else
{
lean_object* x_402; 
lean_dec(x_383);
lean_dec(x_382);
x_402 = lean_ctor_get(x_384, 0);
lean_inc(x_402);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_334);
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_403 = lean_ctor_get(x_384, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_404 = x_384;
} else {
 lean_dec_ref(x_384);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_403);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_384, 1);
lean_inc(x_406);
lean_dec(x_384);
x_407 = lean_box(0);
x_344 = x_407;
x_345 = x_406;
goto block_368;
}
}
}
else
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_381, 0);
lean_inc(x_408);
lean_dec(x_381);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_412 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_412, 0, x_411);
lean_inc(x_334);
x_413 = l_Lean_Elab_Command_throwError___rarg(x_409, x_412, x_334, x_377);
lean_dec(x_409);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_334);
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_416 = x_413;
} else {
 lean_dec_ref(x_413);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_413, 1);
lean_inc(x_418);
lean_dec(x_413);
x_419 = lean_box(0);
x_344 = x_419;
x_345 = x_418;
goto block_368;
}
}
else
{
lean_object* x_420; 
x_420 = lean_box(0);
x_344 = x_420;
x_345 = x_377;
goto block_368;
}
}
}
else
{
lean_object* x_421; 
lean_dec(x_373);
lean_dec(x_370);
x_421 = lean_ctor_get(x_375, 0);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_334);
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_422 = lean_ctor_get(x_375, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_423 = x_375;
} else {
 lean_dec_ref(x_375);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_421);
lean_ctor_set(x_424, 1, x_422);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_375, 1);
lean_inc(x_425);
lean_dec(x_375);
x_426 = lean_box(0);
x_344 = x_426;
x_345 = x_425;
goto block_368;
}
}
}
else
{
lean_object* x_427; 
lean_dec(x_370);
x_427 = lean_ctor_get(x_372, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_334);
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_428 = lean_ctor_get(x_372, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_429 = x_372;
} else {
 lean_dec_ref(x_372);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_372, 1);
lean_inc(x_431);
lean_dec(x_372);
x_432 = lean_box(0);
x_344 = x_432;
x_345 = x_431;
goto block_368;
}
}
block_368:
{
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_346 = l_Lean_Elab_Command_commandElabAttribute;
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
x_348 = l_Lean_PersistentEnvExtension_getState___rarg(x_347, x_343);
lean_dec(x_343);
lean_dec(x_347);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
lean_inc(x_1);
x_350 = l_Lean_Syntax_getKind(x_1);
x_351 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(x_349, x_350);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_341);
x_352 = l_Lean_Name_toString___closed__1;
x_353 = l_Lean_Name_toStringWithSep___main(x_352, x_350);
x_354 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_355 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_355, 0, x_354);
x_356 = l_Lean_Elab_Term_elabUsingElabFns___closed__3;
x_357 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_355);
x_358 = l_Lean_Elab_Term_elabUsingElabFns___closed__6;
x_359 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
x_360 = l_Lean_Elab_Command_throwError___rarg(x_1, x_359, x_334, x_345);
lean_dec(x_1);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_350);
x_361 = lean_ctor_get(x_351, 0);
lean_inc(x_361);
lean_dec(x_351);
x_362 = l___private_Lean_Elab_Command_5__elabCommandUsing___main(x_341, x_1, x_361, x_334, x_345);
return x_362;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_334);
x_363 = lean_ctor_get(x_344, 0);
lean_inc(x_363);
lean_dec(x_344);
lean_inc(x_363);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_1);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_12);
x_366 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_366, 0, x_7);
lean_ctor_set(x_366, 1, x_8);
lean_ctor_set(x_366, 2, x_9);
lean_ctor_set(x_366, 3, x_319);
lean_ctor_set(x_366, 4, x_11);
lean_ctor_set(x_366, 5, x_365);
lean_ctor_set(x_366, 6, x_327);
x_1 = x_363;
x_2 = x_366;
x_3 = x_345;
goto _start;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_334);
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_433 = lean_ctor_get(x_340, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_340, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_435 = x_340;
} else {
 lean_dec_ref(x_340);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
return x_436;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_454 = lean_unsigned_to_nat(0u);
x_455 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(x_336, x_454, x_334, x_333);
lean_dec(x_336);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; 
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_456 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_457 = l_Lean_Elab_Command_throwError___rarg(x_1, x_456, x_334, x_333);
lean_dec(x_1);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_458 = lean_ctor_get(x_332, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_332, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_460 = x_332;
} else {
 lean_dec_ref(x_332);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_462 = lean_ctor_get(x_321, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_321, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_464 = x_321;
} else {
 lean_dec_ref(x_321);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_463);
return x_465;
}
}
}
else
{
lean_object* x_466; lean_object* x_467; uint8_t x_468; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_466 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_467 = l_Lean_Elab_Command_throwError___rarg(x_1, x_466, x_2, x_6);
lean_dec(x_1);
x_468 = !lean_is_exclusive(x_467);
if (x_468 == 0)
{
return x_467;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_467, 0);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_467);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
else
{
uint8_t x_472; 
lean_dec(x_2);
lean_dec(x_1);
x_472 = !lean_is_exclusive(x_4);
if (x_472 == 0)
{
return x_4;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_ctor_get(x_4, 0);
x_474 = lean_ctor_get(x_4, 1);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_4);
x_475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
return x_475;
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Elab_Command_elabCommand___main___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find_x3f___main___at_Lean_Elab_Command_elabCommand___main___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabCommand___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 5);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_3, 5, x_11);
x_12 = l_Lean_Elab_Command_elabCommand___main(x_6, x_3, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 6);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_22, 6, x_19);
x_23 = l_Lean_Elab_Command_elabCommand___main(x_6, x_22, x_7);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_6__mkTermContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_4);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = 1;
x_9 = 0;
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 1, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 2, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 3, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 6, x_10);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get(x_1, 5);
x_17 = lean_ctor_get(x_1, 6);
x_18 = l_Lean_LocalContext_Inhabited___closed__2;
x_19 = l_Array_empty___closed__1;
lean_inc(x_5);
lean_inc(x_14);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_5);
x_21 = lean_ctor_get(x_6, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 4);
lean_inc(x_23);
lean_dec(x_6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
x_24 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_13);
lean_ctor_set(x_24, 3, x_15);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_3);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
lean_ctor_set(x_24, 8, x_16);
lean_ctor_set(x_24, 9, x_17);
lean_ctor_set_uint8(x_24, sizeof(void*)*10, x_8);
lean_ctor_set_uint8(x_24, sizeof(void*)*10 + 1, x_8);
lean_ctor_set_uint8(x_24, sizeof(void*)*10 + 2, x_8);
return x_24;
}
}
lean_object* l___private_Lean_Elab_Command_6__mkTermContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_6__mkTermContext(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Command_7__mkTermState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_MetavarContext_Inhabited___closed__1;
x_6 = l_Lean_Meta_run___rarg___closed__5;
x_7 = l_Lean_NameGenerator_Inhabited___closed__3;
x_8 = l_Lean_TraceState_Inhabited___closed__1;
x_9 = l_PersistentArray_empty___closed__3;
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set(x_10, 5, x_9);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set(x_13, 5, x_4);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Command_7__mkTermState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Command_7__mkTermState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_8__updateState(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_ctor_set(x_1, 3, x_10);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
lean_inc(x_13);
lean_inc(x_12);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_15);
return x_17;
}
}
}
lean_object* l___private_Lean_Elab_Command_8__updateState___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_8__updateState(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Command_9__getVarDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_2);
x_4 = lean_ctor_get(x_3, 6);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Command_9__getVarDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Command_9__getVarDecls(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Command_10__toCommandResult___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Exception_inhabited;
x_2 = l_Lean_Elab_Command_State_inhabited;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Command_10__toCommandResult___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Elab_Command_8__updateState(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = l___private_Lean_Elab_Command_8__updateState(x_1, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l___private_Lean_Elab_Command_8__updateState(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l___private_Lean_Elab_Command_8__updateState(x_1, x_16);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = l___private_Lean_Elab_Command_10__toCommandResult___rarg___closed__1;
x_21 = l_unreachable_x21___rarg(x_20);
return x_21;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_10__toCommandResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_10__toCommandResult___rarg), 2, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Command_10__toCommandResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_10__toCommandResult(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Exception_inhabited___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_CommandElabM_inhabited___closed__1;
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_inhabited(lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_Elab_Command_6__mkTermContext(x_3, x_6, x_1);
x_9 = l___private_Lean_Elab_Command_7__mkTermState(x_6);
lean_dec(x_6);
x_10 = lean_apply_2(x_2, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
x_13 = l___private_Lean_Elab_Command_2__getState(x_3, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_12, 2);
lean_inc(x_18);
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
lean_ctor_set(x_15, 1, x_18);
lean_ctor_set(x_15, 0, x_17);
x_22 = l___private_Lean_Elab_Command_3__setState(x_15, x_3, x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_11);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_15, 2);
x_32 = lean_ctor_get(x_15, 3);
x_33 = lean_ctor_get(x_15, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set(x_34, 4, x_33);
x_35 = l___private_Lean_Elab_Command_3__setState(x_34, x_3, x_16);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_dec(x_10);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_3);
x_50 = l___private_Lean_Elab_Command_2__getState(x_3, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_48, 2);
lean_inc(x_55);
lean_dec(x_48);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
lean_ctor_set(x_52, 1, x_55);
lean_ctor_set(x_52, 0, x_54);
x_59 = l___private_Lean_Elab_Command_3__setState(x_52, x_3, x_53);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_49);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_49);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_52, 2);
x_69 = lean_ctor_get(x_52, 3);
x_70 = lean_ctor_get(x_52, 4);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_52);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_54);
lean_ctor_set(x_71, 1, x_55);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_70);
x_72 = l___private_Lean_Elab_Command_3__setState(x_71, x_3, x_53);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_49);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_49);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_78 = x_72;
} else {
 lean_dec_ref(x_72);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_50);
if (x_80 == 0)
{
return x_50;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_50, 0);
x_82 = lean_ctor_get(x_50, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_50);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_10);
x_84 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_85 = l_unreachable_x21___rarg(x_84);
x_86 = lean_apply_2(x_85, x_3, x_7);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_5);
if (x_87 == 0)
{
return x_5;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_5, 0);
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_5);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_Elab_Command_9__getVarDecls(x_6);
lean_dec(x_6);
lean_inc(x_3);
x_9 = l___private_Lean_Elab_Command_2__getState(x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_Command_6__mkTermContext(x_3, x_10, x_1);
x_13 = l___private_Lean_Elab_Command_7__mkTermState(x_10);
lean_dec(x_10);
x_14 = l_Lean_Elab_Term_elabBinders___rarg(x_8, x_2, x_12, x_13);
lean_dec(x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_3);
x_17 = l___private_Lean_Elab_Command_2__getState(x_3, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_16, 2);
lean_inc(x_22);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_21);
x_26 = l___private_Lean_Elab_Command_3__setState(x_19, x_3, x_20);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_15);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_19, 2);
x_36 = lean_ctor_get(x_19, 3);
x_37 = lean_ctor_get(x_19, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
x_39 = l___private_Lean_Elab_Command_3__setState(x_38, x_3, x_20);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_15);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
return x_17;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_17, 0);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_17);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_14, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_dec(x_14);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_3);
x_54 = l___private_Lean_Elab_Command_2__getState(x_3, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_52, 2);
lean_inc(x_59);
lean_dec(x_52);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
lean_ctor_set(x_56, 1, x_59);
lean_ctor_set(x_56, 0, x_58);
x_63 = l___private_Lean_Elab_Command_3__setState(x_56, x_3, x_57);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 0, x_53);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_53);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 0);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_56, 2);
x_73 = lean_ctor_get(x_56, 3);
x_74 = lean_ctor_get(x_56, 4);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_56);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_58);
lean_ctor_set(x_75, 1, x_59);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_73);
lean_ctor_set(x_75, 4, x_74);
x_76 = l___private_Lean_Elab_Command_3__setState(x_75, x_3, x_57);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
 lean_ctor_set_tag(x_79, 1);
}
lean_ctor_set(x_79, 0, x_53);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_53);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_54);
if (x_84 == 0)
{
return x_54;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_54, 0);
x_86 = lean_ctor_get(x_54, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_54);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_14);
x_88 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_89 = l_unreachable_x21___rarg(x_88);
x_90 = lean_apply_2(x_89, x_3, x_11);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_9);
if (x_91 == 0)
{
return x_9;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_9, 0);
x_93 = lean_ctor_get(x_9, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_9);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_5);
if (x_95 == 0)
{
return x_5;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_5, 0);
x_97 = lean_ctor_get(x_5, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_5);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withLogging(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_2);
x_8 = l___private_Lean_Elab_Command_2__getState(x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_PersistentArray_push___rarg(x_12, x_7);
lean_ctor_set(x_9, 1, x_13);
x_14 = l___private_Lean_Elab_Command_3__setState(x_9, x_2, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
x_27 = lean_ctor_get(x_9, 2);
x_28 = lean_ctor_get(x_9, 3);
x_29 = lean_ctor_get(x_9, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_30 = l_PersistentArray_push___rarg(x_26, x_7);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
x_32 = l___private_Lean_Elab_Command_3__setState(x_31, x_2, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_45);
lean_dec(x_4);
x_46 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_47 = l_unreachable_x21___rarg(x_46);
x_48 = lean_apply_2(x_47, x_2, x_45);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l___private_Lean_Elab_Command_2__getState(x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_PersistentArray_push___rarg(x_16, x_11);
lean_ctor_set(x_13, 1, x_17);
x_18 = l___private_Lean_Elab_Command_3__setState(x_13, x_2, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 2);
x_34 = lean_ctor_get(x_13, 3);
x_35 = lean_ctor_get(x_13, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_36 = l_PersistentArray_push___rarg(x_32, x_11);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
x_38 = l___private_Lean_Elab_Command_3__setState(x_37, x_2, x_14);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_44 = x_38;
} else {
 lean_dec_ref(x_38);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
 lean_ctor_set_tag(x_46, 0);
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_11);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_12);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_12, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_49);
return x_12;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_4, 1);
lean_inc(x_53);
lean_dec(x_4);
x_54 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_55 = l_unreachable_x21___rarg(x_54);
x_56 = lean_apply_2(x_55, x_2, x_53);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set_tag(x_56, 0);
lean_ctor_set(x_56, 0, x_63);
return x_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_dbgTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_7 = lean_dbg_trace(x_5, x_6);
x_8 = lean_apply_2(x_7, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_dbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_dbgTrace___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_setEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_1);
x_9 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
x_23 = lean_ctor_get(x_5, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = l___private_Lean_Elab_Command_3__setState(x_24, x_2, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_4);
if (x_34 == 0)
{
return x_4;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_4, 0);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_Command_getCurrNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_11__addScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l___private_Lean_Elab_Command_2__getState(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_3);
x_12 = l_Lean_Environment_registerNamespace___main(x_10, x_3);
x_13 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 3);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 3, x_3);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_1);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_7, 2, x_18);
lean_ctor_set(x_7, 0, x_12);
x_19 = l___private_Lean_Elab_Command_3__setState(x_7, x_4, x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_13, 2);
x_31 = lean_ctor_get(x_13, 4);
x_32 = lean_ctor_get(x_13, 5);
x_33 = lean_ctor_get(x_13, 6);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_3);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
lean_ctor_set(x_34, 6, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
lean_ctor_set(x_7, 2, x_35);
lean_ctor_set(x_7, 0, x_12);
x_36 = l___private_Lean_Elab_Command_3__setState(x_7, x_4, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
x_47 = lean_ctor_get(x_7, 2);
x_48 = lean_ctor_get(x_7, 3);
x_49 = lean_ctor_get(x_7, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
lean_inc(x_3);
x_50 = l_Lean_Environment_registerNamespace___main(x_45, x_3);
x_51 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_47);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 6);
lean_inc(x_55);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 lean_ctor_release(x_51, 5);
 lean_ctor_release(x_51, 6);
 x_56 = x_51;
} else {
 lean_dec_ref(x_51);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 7, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_2);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_3);
lean_ctor_set(x_57, 4, x_53);
lean_ctor_set(x_57, 5, x_54);
lean_ctor_set(x_57, 6, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_47);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_46);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_48);
lean_ctor_set(x_59, 4, x_49);
x_60 = l___private_Lean_Elab_Command_3__setState(x_59, x_4, x_8);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_6);
if (x_69 == 0)
{
return x_6;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_6, 0);
x_71 = lean_ctor_get(x_6, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_6);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Command_12__addScopes___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid scope");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Command_12__addScopes___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_12__addScopes___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Command_12__addScopes___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_12__addScopes___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_12__addScopes___main(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_2, x_3, x_9, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_5);
x_13 = l_Lean_Elab_Command_getCurrNamespace(x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
if (x_3 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Command_11__addScope(x_2, x_10, x_14, x_5, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
lean_inc(x_10);
x_20 = lean_name_mk_string(x_19, x_10);
x_21 = l_Lean_Name_append___main(x_17, x_20);
lean_dec(x_17);
x_22 = l___private_Lean_Elab_Command_11__addScope(x_2, x_10, x_21, x_5, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
default: 
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_2);
x_31 = l___private_Lean_Elab_Command_12__addScopes___main___closed__3;
x_32 = l_Lean_Elab_Command_throwError___rarg(x_1, x_31, x_5, x_6);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_12__addScopes___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Command_12__addScopes(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Command_12__addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Elab_Command_12__addScopes(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Command_13__addNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_6 = 1;
x_7 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Command_13__addNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Command_13__addNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Command_namespace___elambda__1___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_getId(x_15);
lean_dec(x_15);
x_17 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_18 = 1;
x_19 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_17, x_18, x_16, x_2, x_3);
lean_dec(x_1);
return x_19;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNamespace), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_namespace___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_inc(x_1);
x_47 = l_Lean_Syntax_isOfKind(x_1, x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = 0;
x_4 = x_48;
goto block_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = l_Lean_Syntax_getArgs(x_1);
x_50 = lean_array_get_size(x_49);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_dec_eq(x_50, x_51);
lean_dec(x_50);
x_4 = x_52;
goto block_45;
}
block_45:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_nullKind___closed__2;
lean_inc(x_8);
x_10 = l_Lean_Syntax_isOfKind(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_41; 
x_41 = 0;
x_11 = x_41;
goto block_40;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_Syntax_getArgs(x_8);
x_43 = lean_array_get_size(x_42);
lean_dec(x_42);
x_44 = lean_nat_dec_eq(x_43, x_7);
lean_dec(x_43);
x_11 = x_44;
goto block_40;
}
block_40:
{
if (x_11 == 0)
{
lean_dec(x_1);
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_2);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; 
lean_inc(x_2);
x_20 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_24 = l_String_splitAux___main___closed__1;
x_25 = l___private_Lean_Elab_Command_11__addScope(x_23, x_24, x_21, x_2, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Syntax_getArg(x_8, x_30);
lean_dec(x_8);
x_32 = l_Lean_identKind___closed__2;
lean_inc(x_31);
x_33 = l_Lean_Syntax_isOfKind(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = l_Lean_Syntax_getId(x_31);
lean_dec(x_31);
x_37 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_38 = 0;
x_39 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_37, x_38, x_36, x_2, x_3);
lean_dec(x_1);
return x_39;
}
}
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSection), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_section___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSection___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getScopes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_2__getState(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
uint8_t l___private_Lean_Elab_Command_14__checkAnonymousScope(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
x_5 = l_String_splitAux___main___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Command_14__checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Command_14__checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Command_15__checkEndHeader___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_string_dec_eq(x_9, x_7);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
}
default: 
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_15__checkEndHeader___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Command_15__checkEndHeader___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Lean_Elab_Command_15__checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Elab_Command_15__checkEndHeader___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Command_15__checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Command_15__checkEndHeader(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name is missing");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name mismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', insufficient scopes");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_101; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getOptionalIdent_x3f(x_5);
lean_dec(x_5);
lean_inc(x_2);
x_101 = l_Lean_Elab_Command_getScopes(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_7 = x_4;
x_8 = x_102;
x_9 = x_103;
goto block_100;
}
else
{
uint8_t x_104; 
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_6, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_dec(x_101);
x_111 = l_Lean_Name_getNumParts___main(x_108);
lean_dec(x_108);
x_7 = x_111;
x_8 = x_109;
x_9 = x_110;
goto block_100;
}
else
{
uint8_t x_112; 
lean_dec(x_6);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_101);
if (x_112 == 0)
{
return x_101;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_101, 0);
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_101);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
block_100:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___main___rarg(x_8, x_10);
x_12 = lean_nat_dec_lt(x_7, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_2);
x_26 = l___private_Lean_Elab_Command_2__getState(x_2, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 2);
x_31 = l_List_lengthAux___main___rarg(x_30, x_10);
x_32 = lean_nat_sub(x_31, x_4);
lean_dec(x_31);
x_33 = l_List_drop___main___rarg(x_32, x_30);
lean_dec(x_30);
lean_ctor_set(x_27, 2, x_33);
lean_inc(x_2);
x_34 = l___private_Lean_Elab_Command_3__setState(x_27, x_2, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Command_elabEnd___closed__9;
x_37 = l_Lean_Elab_Command_throwError___rarg(x_1, x_36, x_2, x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
x_48 = lean_ctor_get(x_27, 2);
x_49 = lean_ctor_get(x_27, 3);
x_50 = lean_ctor_get(x_27, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_51 = l_List_lengthAux___main___rarg(x_48, x_10);
x_52 = lean_nat_sub(x_51, x_4);
lean_dec(x_51);
x_53 = l_List_drop___main___rarg(x_52, x_48);
lean_dec(x_48);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_49);
lean_ctor_set(x_54, 4, x_50);
lean_inc(x_2);
x_55 = l___private_Lean_Elab_Command_3__setState(x_54, x_2, x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Elab_Command_elabEnd___closed__9;
x_58 = l_Lean_Elab_Command_throwError___rarg(x_1, x_57, x_2, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_26);
if (x_67 == 0)
{
return x_26;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_26, 0);
x_69 = lean_ctor_get(x_26, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_26);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_inc(x_2);
x_71 = l___private_Lean_Elab_Command_2__getState(x_2, x_9);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 2);
x_76 = l_List_drop___main___rarg(x_7, x_75);
lean_dec(x_75);
lean_ctor_set(x_72, 2, x_76);
lean_inc(x_2);
x_77 = l___private_Lean_Elab_Command_3__setState(x_72, x_2, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_13 = x_78;
goto block_25;
}
else
{
uint8_t x_79; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 0);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_77);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_72, 0);
x_84 = lean_ctor_get(x_72, 1);
x_85 = lean_ctor_get(x_72, 2);
x_86 = lean_ctor_get(x_72, 3);
x_87 = lean_ctor_get(x_72, 4);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_72);
x_88 = l_List_drop___main___rarg(x_7, x_85);
lean_dec(x_85);
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_86);
lean_ctor_set(x_89, 4, x_87);
lean_inc(x_2);
x_90 = l___private_Lean_Elab_Command_3__setState(x_89, x_2, x_73);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_13 = x_91;
goto block_25;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_71);
if (x_96 == 0)
{
return x_71;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_71, 0);
x_98 = lean_ctor_get(x_71, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_71);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
block_25:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_14; 
x_14 = l___private_Lean_Elab_Command_14__checkAnonymousScope(x_8);
lean_dec(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_Command_elabEnd___closed__3;
x_16 = l_Lean_Elab_Command_throwError___rarg(x_1, x_15, x_2, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l___private_Lean_Elab_Command_15__checkEndHeader___main(x_19, x_8);
lean_dec(x_8);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Command_elabEnd___closed__6;
x_22 = l_Lean_Elab_Command_throwError___rarg(x_1, x_21, x_2, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabEnd(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_end___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_7 = 1;
lean_inc(x_4);
lean_inc(x_2);
x_8 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_6, x_7, x_2, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_4);
x_10 = lean_apply_2(x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_Command_2__getState(x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 2);
x_18 = l_Lean_Name_getNumParts___main(x_2);
lean_dec(x_2);
x_19 = l_List_drop___main___rarg(x_18, x_17);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_19);
x_20 = l___private_Lean_Elab_Command_3__setState(x_14, x_4, x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
x_31 = lean_ctor_get(x_14, 2);
x_32 = lean_ctor_get(x_14, 3);
x_33 = lean_ctor_get(x_14, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_34 = l_Lean_Name_getNumParts___main(x_2);
lean_dec(x_2);
x_35 = l_List_drop___main___rarg(x_34, x_31);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_33);
x_37 = l___private_Lean_Elab_Command_3__setState(x_36, x_4, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_10);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_8);
if (x_53 == 0)
{
return x_8;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_8, 0);
x_55 = lean_ctor_get(x_8, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_8);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l_Lean_Elab_Command_withNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withNamespace___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withNamespace___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_withNamespace___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Monad;
x_2 = l_Lean_Elab_Command_Scope_inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_modifyScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_apply_1(x_1, x_43);
lean_ctor_set(x_6, 0, x_44);
x_45 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_45, 0);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_6, 0);
x_57 = lean_ctor_get(x_6, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_6);
x_58 = lean_apply_1(x_1, x_56);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_5, 2, x_59);
x_60 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_5, 0);
x_70 = lean_ctor_get(x_5, 1);
x_71 = lean_ctor_get(x_5, 3);
x_72 = lean_ctor_get(x_5, 4);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_5);
x_73 = lean_ctor_get(x_6, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_75 = x_6;
} else {
 lean_dec_ref(x_6);
 x_75 = lean_box(0);
}
x_76 = lean_apply_1(x_1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_78, 3, x_71);
lean_ctor_set(x_78, 4, x_72);
x_79 = l___private_Lean_Elab_Command_3__setState(x_78, x_2, x_39);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_4);
if (x_88 == 0)
{
return x_4;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_4, 0);
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_4);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 5);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 5);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a universe level named '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerAttributeImplBuilder___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_2);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Command_throwError___rarg(x_1, x_12, x_3, x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_6, 1);
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 5);
lean_ctor_set(x_6, 1, x_47);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_39, 5, x_6);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_5, 2, x_48);
x_49 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_39, 0);
x_61 = lean_ctor_get(x_39, 1);
x_62 = lean_ctor_get(x_39, 2);
x_63 = lean_ctor_get(x_39, 3);
x_64 = lean_ctor_get(x_39, 4);
x_65 = lean_ctor_get(x_39, 5);
x_66 = lean_ctor_get(x_39, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_39);
lean_ctor_set(x_6, 1, x_65);
lean_ctor_set(x_6, 0, x_1);
x_67 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_63);
lean_ctor_set(x_67, 4, x_64);
lean_ctor_set(x_67, 5, x_6);
lean_ctor_set(x_67, 6, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_44);
lean_ctor_set(x_5, 2, x_68);
x_69 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_6, 1);
lean_inc(x_78);
lean_dec(x_6);
x_79 = lean_ctor_get(x_39, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_39, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_39, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_39, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_39, 6);
lean_inc(x_85);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_86 = x_39;
} else {
 lean_dec_ref(x_39);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 7, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_81);
lean_ctor_set(x_88, 3, x_82);
lean_ctor_set(x_88, 4, x_83);
lean_ctor_set(x_88, 5, x_87);
lean_ctor_set(x_88, 6, x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_78);
lean_ctor_set(x_5, 2, x_89);
x_90 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_99 = lean_ctor_get(x_5, 0);
x_100 = lean_ctor_get(x_5, 1);
x_101 = lean_ctor_get(x_5, 3);
x_102 = lean_ctor_get(x_5, 4);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_5);
x_103 = lean_ctor_get(x_6, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_104 = x_6;
} else {
 lean_dec_ref(x_6);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_39, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_39, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_39, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_39, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_39, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_39, 5);
lean_inc(x_110);
x_111 = lean_ctor_get(x_39, 6);
lean_inc(x_111);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_112 = x_39;
} else {
 lean_dec_ref(x_39);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_104;
}
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_110);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 7, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_107);
lean_ctor_set(x_114, 3, x_108);
lean_ctor_set(x_114, 4, x_109);
lean_ctor_set(x_114, 5, x_113);
lean_ctor_set(x_114, 6, x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_103);
x_116 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_100);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set(x_116, 3, x_101);
lean_ctor_set(x_116, 4, x_102);
x_117 = l___private_Lean_Elab_Command_3__setState(x_116, x_2, x_40);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_4);
if (x_126 == 0)
{
return x_4;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_4, 0);
x_128 = lean_ctor_get(x_4, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_4);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Syntax_getId(x_1);
lean_inc(x_2);
x_5 = l_Lean_Elab_Command_getLevelNames(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_4, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(x_4, x_2, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(x_1, x_4, x_2, x_7);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_addUnivLevel(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
x_10 = l_Lean_Elab_Command_elabCommand___main(x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
x_4 = x_16;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabChoiceAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabChoiceAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabChoiceAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elbChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Syntax_getArgs(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Elab_Command_elabChoiceAux___main(x_4, x_5, x_2, x_3);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elbChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elbChoice(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elbChoice___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_choiceKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Elab_Command_addUnivLevel(x_5, x_2, x_3);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabUniverse(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverse___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_universe___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_5);
x_13 = l_Lean_Elab_Command_addUnivLevel(x_10, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_3 = x_12;
x_4 = x_14;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(0);
x_9 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(x_1, x_6, x_7, x_8, x_2, x_3);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabUniverses(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverses___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_universes___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(4);
x_8 = lean_add_decl(x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_Elab_Command_getOptions(x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_KernelException_toMessageData(x_9, x_11);
x_14 = l_Lean_Elab_Command_throwError___rarg(x_1, x_13, x_2, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = l_Lean_Elab_Command_setEnv(x_19, x_2, x_6);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabInitQuot(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_init__quot___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getOpenDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_logUnknownDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addClass___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_logUnknownDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_logUnknownDecl___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_2);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_Command_logUnknownDecl___closed__2;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 2;
x_14 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_13, x_12, x_3, x_4);
return x_14;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_logUnknownDecl(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_resolveNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getOpenDecls(x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_resolveNamespace(x_5, x_8, x_12, x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_box(1);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = l_Lean_Elab_resolveNamespace(x_5, x_8, x_16, x_1);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
return x_4;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = l_Lean_Syntax_getId(x_13);
lean_inc(x_16);
x_17 = l_Lean_Name_append___main(x_2, x_16);
lean_inc(x_4);
x_18 = l_Lean_Environment_contains(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_inc(x_8);
x_19 = l_Lean_Elab_Command_logUnknownDecl(x_13, x_17, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_6 = x_15;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
x_26 = l_Lean_Name_append___main(x_3, x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_7);
x_6 = x_15;
x_7 = x_28;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_add_alias(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'export', self export");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabExport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabExport(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getIdAt(x_1, x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Command_resolveNamespace(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_name_eq(x_7, x_10);
if (x_12 == 0)
{
x_13 = x_11;
goto block_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_10);
lean_dec(x_7);
x_71 = l_Lean_Elab_Command_elabExport___closed__3;
x_72 = l_Lean_Elab_Command_throwError___rarg(x_1, x_71, x_2, x_11);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
block_70:
{
lean_object* x_14; 
lean_inc(x_2);
x_14 = l_Lean_Elab_Command_getEnv(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_22 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(x_1, x_7, x_10, x_15, x_19, x_21, x_20, x_2, x_16);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_2);
x_25 = l___private_Lean_Elab_Command_2__getState(x_2, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_29, x_23);
lean_ctor_set(x_26, 0, x_30);
x_31 = l___private_Lean_Elab_Command_3__setState(x_26, x_2, x_27);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
x_44 = lean_ctor_get(x_26, 2);
x_45 = lean_ctor_get(x_26, 3);
x_46 = lean_ctor_get(x_26, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_26);
x_47 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_42, x_23);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_45);
lean_ctor_set(x_48, 4, x_46);
x_49 = l___private_Lean_Elab_Command_3__setState(x_48, x_2, x_27);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_56 = x_49;
} else {
 lean_dec_ref(x_49);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_23);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_25);
if (x_58 == 0)
{
return x_25;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_25, 0);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_25);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_22);
if (x_62 == 0)
{
return x_22;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_22, 0);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_22);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_14);
if (x_66 == 0)
{
return x_14;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_14, 0);
x_68 = lean_ctor_get(x_14, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_14);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_7);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
return x_9;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_9, 0);
x_79 = lean_ctor_get(x_9, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_9);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_6);
if (x_81 == 0)
{
return x_6;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_6, 0);
x_83 = lean_ctor_get(x_6, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_6);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabExport(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabExport___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_export___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_6, 1);
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 4);
lean_ctor_set(x_6, 1, x_47);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_39, 4, x_6);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_5, 2, x_48);
x_49 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_39, 0);
x_61 = lean_ctor_get(x_39, 1);
x_62 = lean_ctor_get(x_39, 2);
x_63 = lean_ctor_get(x_39, 3);
x_64 = lean_ctor_get(x_39, 4);
x_65 = lean_ctor_get(x_39, 5);
x_66 = lean_ctor_get(x_39, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_39);
lean_ctor_set(x_6, 1, x_64);
lean_ctor_set(x_6, 0, x_1);
x_67 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_63);
lean_ctor_set(x_67, 4, x_6);
lean_ctor_set(x_67, 5, x_65);
lean_ctor_set(x_67, 6, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_44);
lean_ctor_set(x_5, 2, x_68);
x_69 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_6, 1);
lean_inc(x_78);
lean_dec(x_6);
x_79 = lean_ctor_get(x_39, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_39, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_39, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_39, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_39, 6);
lean_inc(x_85);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_86 = x_39;
} else {
 lean_dec_ref(x_39);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_83);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 7, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_81);
lean_ctor_set(x_88, 3, x_82);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_84);
lean_ctor_set(x_88, 6, x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_78);
lean_ctor_set(x_5, 2, x_89);
x_90 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_99 = lean_ctor_get(x_5, 0);
x_100 = lean_ctor_get(x_5, 1);
x_101 = lean_ctor_get(x_5, 3);
x_102 = lean_ctor_get(x_5, 4);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_5);
x_103 = lean_ctor_get(x_6, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_104 = x_6;
} else {
 lean_dec_ref(x_6);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_39, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_39, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_39, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_39, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_39, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_39, 5);
lean_inc(x_110);
x_111 = lean_ctor_get(x_39, 6);
lean_inc(x_111);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_112 = x_39;
} else {
 lean_dec_ref(x_39);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_104;
}
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_109);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 7, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_107);
lean_ctor_set(x_114, 3, x_108);
lean_ctor_set(x_114, 4, x_113);
lean_ctor_set(x_114, 5, x_110);
lean_ctor_set(x_114, 6, x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_103);
x_116 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_100);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set(x_116, 3, x_101);
lean_ctor_set(x_116, 4, x_102);
x_117 = l___private_Lean_Elab_Command_3__setState(x_116, x_2, x_40);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_4);
if (x_126 == 0)
{
return x_4;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_4, 0);
x_128 = lean_ctor_get(x_4, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_4);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Syntax_getId(x_10);
lean_dec(x_10);
lean_inc(x_5);
x_14 = l_Lean_Elab_Command_resolveNamespace(x_13, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_5);
x_19 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_18, x_5, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_3 = x_12;
x_4 = x_20;
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_4, x_8, x_6, x_9, x_2, x_3);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpenSimple(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = l_Lean_Syntax_getId(x_11);
lean_inc(x_14);
x_15 = l_Lean_Name_append___main(x_2, x_14);
lean_inc(x_6);
x_16 = l_Lean_Elab_Command_getEnv(x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Environment_contains(x_17, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_6);
x_20 = l_Lean_Elab_Command_logUnknownDecl(x_11, x_15, x_6, x_18);
lean_dec(x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_4 = x_13;
x_5 = x_21;
x_7 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_15);
lean_inc(x_6);
x_29 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_28, x_6, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_4 = x_13;
x_5 = x_30;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_6);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_array_get(x_5, x_4, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_4, x_10, x_14, x_6, x_15, x_2, x_11);
lean_dec(x_14);
lean_dec(x_10);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpenOnly(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = l_Lean_Syntax_getId(x_12);
lean_inc(x_15);
x_16 = l_Lean_Name_append___main(x_2, x_15);
lean_inc(x_3);
x_17 = l_Lean_Environment_contains(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_inc(x_7);
x_18 = l_Lean_Elab_Command_logUnknownDecl(x_12, x_16, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_5 = x_14;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_6);
x_5 = x_14;
x_6 = x_25;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l_Lean_Elab_Command_getEnv(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_array_get(x_5, x_4, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
lean_inc(x_2);
x_19 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_4, x_10, x_13, x_18, x_6, x_17, x_2, x_14);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_22, x_2, x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpenHiding(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getIdAt(x_11, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getIdAt(x_11, x_14);
x_16 = l_Lean_Name_append___main(x_1, x_13);
lean_inc(x_6);
x_17 = l_Lean_Elab_Command_getEnv(x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Environment_contains(x_18, x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
lean_inc(x_6);
x_21 = l_Lean_Elab_Command_logUnknownDecl(x_11, x_16, x_6, x_19);
lean_dec(x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_24;
x_5 = x_22;
x_7 = x_23;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_16);
lean_inc(x_6);
x_31 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_30, x_6, x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_34;
x_5 = x_32;
x_7 = x_33;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_array_get(x_5, x_4, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_10, x_12, x_14, x_6, x_15, x_2, x_11);
lean_dec(x_14);
lean_dec(x_10);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpenRenaming(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_asNode(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
x_9 = lean_name_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
x_11 = lean_name_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
x_13 = lean_name_eq(x_7, x_12);
lean_dec(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Command_elabOpenRenaming(x_6, x_2, x_3);
lean_dec(x_6);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_elabOpenHiding(x_6, x_2, x_3);
lean_dec(x_6);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
x_16 = l_Lean_Elab_Command_elabOpenOnly(x_6, x_2, x_3);
lean_dec(x_6);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = l_Lean_Elab_Command_elabOpenSimple(x_6, x_2, x_3);
lean_dec(x_6);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpen(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabOpen___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_open___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 6);
x_47 = lean_array_push(x_46, x_1);
lean_ctor_set(x_39, 6, x_47);
x_48 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_39, 0);
x_60 = lean_ctor_get(x_39, 1);
x_61 = lean_ctor_get(x_39, 2);
x_62 = lean_ctor_get(x_39, 3);
x_63 = lean_ctor_get(x_39, 4);
x_64 = lean_ctor_get(x_39, 5);
x_65 = lean_ctor_get(x_39, 6);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_39);
x_66 = lean_array_push(x_65, x_1);
x_67 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_62);
lean_ctor_set(x_67, 4, x_63);
lean_ctor_set(x_67, 5, x_64);
lean_ctor_set(x_67, 6, x_66);
lean_ctor_set(x_6, 0, x_67);
x_68 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_6, 1);
lean_inc(x_77);
lean_dec(x_6);
x_78 = lean_ctor_get(x_39, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_39, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_39, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_39, 6);
lean_inc(x_84);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_85 = x_39;
} else {
 lean_dec_ref(x_39);
 x_85 = lean_box(0);
}
x_86 = lean_array_push(x_84, x_1);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 7, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_80);
lean_ctor_set(x_87, 3, x_81);
lean_ctor_set(x_87, 4, x_82);
lean_ctor_set(x_87, 5, x_83);
lean_ctor_set(x_87, 6, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
lean_ctor_set(x_5, 2, x_88);
x_89 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_98 = lean_ctor_get(x_5, 0);
x_99 = lean_ctor_get(x_5, 1);
x_100 = lean_ctor_get(x_5, 3);
x_101 = lean_ctor_get(x_5, 4);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_5);
x_102 = lean_ctor_get(x_6, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_103 = x_6;
} else {
 lean_dec_ref(x_6);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_39, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_39, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_39, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_39, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_39, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_39, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_39, 6);
lean_inc(x_110);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_111 = x_39;
} else {
 lean_dec_ref(x_39);
 x_111 = lean_box(0);
}
x_112 = lean_array_push(x_110, x_1);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 7, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_104);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_106);
lean_ctor_set(x_113, 3, x_107);
lean_ctor_set(x_113, 4, x_108);
lean_ctor_set(x_113, 5, x_109);
lean_ctor_set(x_113, 6, x_112);
if (lean_is_scalar(x_103)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_103;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_102);
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_98);
lean_ctor_set(x_115, 1, x_99);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_100);
lean_ctor_set(x_115, 4, x_101);
x_116 = l___private_Lean_Elab_Command_3__setState(x_115, x_2, x_40);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_123 = x_116;
} else {
 lean_dec_ref(x_116);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_4);
if (x_125 == 0)
{
return x_4;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_4, 0);
x_127 = lean_ctor_get(x_4, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_4);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 6);
x_47 = lean_array_push(x_46, x_1);
lean_ctor_set(x_39, 6, x_47);
x_48 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_39, 0);
x_60 = lean_ctor_get(x_39, 1);
x_61 = lean_ctor_get(x_39, 2);
x_62 = lean_ctor_get(x_39, 3);
x_63 = lean_ctor_get(x_39, 4);
x_64 = lean_ctor_get(x_39, 5);
x_65 = lean_ctor_get(x_39, 6);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_39);
x_66 = lean_array_push(x_65, x_1);
x_67 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_62);
lean_ctor_set(x_67, 4, x_63);
lean_ctor_set(x_67, 5, x_64);
lean_ctor_set(x_67, 6, x_66);
lean_ctor_set(x_6, 0, x_67);
x_68 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_6, 1);
lean_inc(x_77);
lean_dec(x_6);
x_78 = lean_ctor_get(x_39, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_39, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_39, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_39, 6);
lean_inc(x_84);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_85 = x_39;
} else {
 lean_dec_ref(x_39);
 x_85 = lean_box(0);
}
x_86 = lean_array_push(x_84, x_1);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 7, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_80);
lean_ctor_set(x_87, 3, x_81);
lean_ctor_set(x_87, 4, x_82);
lean_ctor_set(x_87, 5, x_83);
lean_ctor_set(x_87, 6, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
lean_ctor_set(x_5, 2, x_88);
x_89 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_98 = lean_ctor_get(x_5, 0);
x_99 = lean_ctor_get(x_5, 1);
x_100 = lean_ctor_get(x_5, 3);
x_101 = lean_ctor_get(x_5, 4);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_5);
x_102 = lean_ctor_get(x_6, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_103 = x_6;
} else {
 lean_dec_ref(x_6);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_39, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_39, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_39, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_39, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_39, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_39, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_39, 6);
lean_inc(x_110);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_111 = x_39;
} else {
 lean_dec_ref(x_39);
 x_111 = lean_box(0);
}
x_112 = lean_array_push(x_110, x_1);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 7, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_104);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_106);
lean_ctor_set(x_113, 3, x_107);
lean_ctor_set(x_113, 4, x_108);
lean_ctor_set(x_113, 5, x_109);
lean_ctor_set(x_113, 6, x_112);
if (lean_is_scalar(x_103)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_103;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_102);
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_98);
lean_ctor_set(x_115, 1, x_99);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_100);
lean_ctor_set(x_115, 4, x_101);
x_116 = l___private_Lean_Elab_Command_3__setState(x_115, x_2, x_40);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_123 = x_116;
} else {
 lean_dec_ref(x_116);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_4);
if (x_125 == 0)
{
return x_4;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_4, 0);
x_127 = lean_ctor_get(x_4, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_4);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_mkOptionalNode___closed__2;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_8 = l_Lean_Elab_Term_elabBinders___rarg(x_6, x_7, x_3, x_4);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__1___boxed), 4, 1);
lean_closure_set(x_7, 0, x_5);
lean_inc(x_2);
x_8 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_Command_9__getVarDecls(x_9);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l___private_Lean_Elab_Command_2__getState(x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_Command_6__mkTermContext(x_2, x_13, x_6);
x_16 = l___private_Lean_Elab_Command_7__mkTermState(x_13);
lean_dec(x_13);
x_17 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_7, x_15, x_16);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_2);
x_19 = l___private_Lean_Elab_Command_2__getState(x_2, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_18, 2);
lean_inc(x_24);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
lean_ctor_set(x_21, 1, x_24);
lean_ctor_set(x_21, 0, x_23);
lean_inc(x_2);
x_28 = l___private_Lean_Elab_Command_3__setState(x_21, x_2, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_5, x_2, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_21, 2);
x_36 = lean_ctor_get(x_21, 3);
x_37 = lean_ctor_get(x_21, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
lean_inc(x_2);
x_39 = l___private_Lean_Elab_Command_3__setState(x_38, x_2, x_22);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_5, x_2, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_5);
lean_dec(x_2);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_44 = x_39;
} else {
 lean_dec_ref(x_39);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
return x_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_17, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_5);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_dec(x_17);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_2);
x_53 = l___private_Lean_Elab_Command_2__getState(x_2, x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_51, 2);
lean_inc(x_58);
lean_dec(x_51);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
lean_ctor_set(x_55, 1, x_58);
lean_ctor_set(x_55, 0, x_57);
x_62 = l___private_Lean_Elab_Command_3__setState(x_55, x_2, x_56);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_52);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_52);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_52);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_55, 2);
x_72 = lean_ctor_get(x_55, 3);
x_73 = lean_ctor_get(x_55, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_55);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_57);
lean_ctor_set(x_74, 1, x_58);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
x_75 = l___private_Lean_Elab_Command_3__setState(x_74, x_2, x_56);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_52);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_52);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_53);
if (x_83 == 0)
{
return x_53;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_53, 0);
x_85 = lean_ctor_get(x_53, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_53);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_17);
x_87 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_88 = l_unreachable_x21___rarg(x_87);
lean_inc(x_2);
x_89 = lean_apply_2(x_88, x_2, x_14);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__2(x_5, x_2, x_90);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_5);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
return x_12;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_12, 0);
x_98 = lean_ctor_get(x_12, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_12);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_8);
if (x_100 == 0)
{
return x_8;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_8, 0);
x_102 = lean_ctor_get(x_8, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_8);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabVariable___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabVariable(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_variable___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_39, 6);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_47, x_46);
lean_ctor_set(x_39, 6, x_48);
x_49 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_39, 0);
x_61 = lean_ctor_get(x_39, 1);
x_62 = lean_ctor_get(x_39, 2);
x_63 = lean_ctor_get(x_39, 3);
x_64 = lean_ctor_get(x_39, 4);
x_65 = lean_ctor_get(x_39, 5);
x_66 = lean_ctor_get(x_39, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_39);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_67, x_66);
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_64);
lean_ctor_set(x_69, 5, x_65);
lean_ctor_set(x_69, 6, x_68);
lean_ctor_set(x_6, 0, x_69);
x_70 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_ctor_get(x_6, 1);
lean_inc(x_79);
lean_dec(x_6);
x_80 = lean_ctor_get(x_39, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_39, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_39, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_39, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_39, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_39, 6);
lean_inc(x_86);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_87 = x_39;
} else {
 lean_dec_ref(x_39);
 x_87 = lean_box(0);
}
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_88, x_86);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 7, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_81);
lean_ctor_set(x_90, 2, x_82);
lean_ctor_set(x_90, 3, x_83);
lean_ctor_set(x_90, 4, x_84);
lean_ctor_set(x_90, 5, x_85);
lean_ctor_set(x_90, 6, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_79);
lean_ctor_set(x_5, 2, x_91);
x_92 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_101 = lean_ctor_get(x_5, 0);
x_102 = lean_ctor_get(x_5, 1);
x_103 = lean_ctor_get(x_5, 3);
x_104 = lean_ctor_get(x_5, 4);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_5);
x_105 = lean_ctor_get(x_6, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_106 = x_6;
} else {
 lean_dec_ref(x_6);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_39, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_39, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_39, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_39, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_39, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_39, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_39, 6);
lean_inc(x_113);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_114 = x_39;
} else {
 lean_dec_ref(x_39);
 x_114 = lean_box(0);
}
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_115, x_113);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 7, 0);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_108);
lean_ctor_set(x_117, 2, x_109);
lean_ctor_set(x_117, 3, x_110);
lean_ctor_set(x_117, 4, x_111);
lean_ctor_set(x_117, 5, x_112);
lean_ctor_set(x_117, 6, x_116);
if (lean_is_scalar(x_106)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_106;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_105);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_101);
lean_ctor_set(x_119, 1, x_102);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_103);
lean_ctor_set(x_119, 4, x_104);
x_120 = l___private_Lean_Elab_Command_3__setState(x_119, x_2, x_40);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_4);
if (x_129 == 0)
{
return x_4;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_4, 0);
x_131 = lean_ctor_get(x_4, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_4);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_39, 6);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_47, x_46);
lean_ctor_set(x_39, 6, x_48);
x_49 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_39, 0);
x_61 = lean_ctor_get(x_39, 1);
x_62 = lean_ctor_get(x_39, 2);
x_63 = lean_ctor_get(x_39, 3);
x_64 = lean_ctor_get(x_39, 4);
x_65 = lean_ctor_get(x_39, 5);
x_66 = lean_ctor_get(x_39, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_39);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_67, x_66);
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_64);
lean_ctor_set(x_69, 5, x_65);
lean_ctor_set(x_69, 6, x_68);
lean_ctor_set(x_6, 0, x_69);
x_70 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_ctor_get(x_6, 1);
lean_inc(x_79);
lean_dec(x_6);
x_80 = lean_ctor_get(x_39, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_39, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_39, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_39, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_39, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_39, 6);
lean_inc(x_86);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_87 = x_39;
} else {
 lean_dec_ref(x_39);
 x_87 = lean_box(0);
}
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_88, x_86);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 7, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_81);
lean_ctor_set(x_90, 2, x_82);
lean_ctor_set(x_90, 3, x_83);
lean_ctor_set(x_90, 4, x_84);
lean_ctor_set(x_90, 5, x_85);
lean_ctor_set(x_90, 6, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_79);
lean_ctor_set(x_5, 2, x_91);
x_92 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_101 = lean_ctor_get(x_5, 0);
x_102 = lean_ctor_get(x_5, 1);
x_103 = lean_ctor_get(x_5, 3);
x_104 = lean_ctor_get(x_5, 4);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_5);
x_105 = lean_ctor_get(x_6, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_106 = x_6;
} else {
 lean_dec_ref(x_6);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_39, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_39, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_39, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_39, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_39, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_39, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_39, 6);
lean_inc(x_113);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_114 = x_39;
} else {
 lean_dec_ref(x_39);
 x_114 = lean_box(0);
}
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_115, x_113);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 7, 0);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_108);
lean_ctor_set(x_117, 2, x_109);
lean_ctor_set(x_117, 3, x_110);
lean_ctor_set(x_117, 4, x_111);
lean_ctor_set(x_117, 5, x_112);
lean_ctor_set(x_117, 6, x_116);
if (lean_is_scalar(x_106)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_106;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_105);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_101);
lean_ctor_set(x_119, 1, x_102);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_103);
lean_ctor_set(x_119, 4, x_104);
x_120 = l___private_Lean_Elab_Command_3__setState(x_119, x_2, x_40);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_4);
if (x_129 == 0)
{
return x_4;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_4, 0);
x_131 = lean_ctor_get(x_4, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_4);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_6 = l_Lean_Elab_Term_elabBinders___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabVariables(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___lambda__1___boxed), 4, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_Command_9__getVarDecls(x_10);
lean_dec(x_10);
lean_inc(x_2);
x_13 = l___private_Lean_Elab_Command_2__getState(x_2, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Command_6__mkTermContext(x_2, x_14, x_7);
x_17 = l___private_Lean_Elab_Command_7__mkTermState(x_14);
lean_dec(x_14);
x_18 = l_Lean_Elab_Term_elabBinders___rarg(x_12, x_8, x_16, x_17);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Command_2__getState(x_2, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_19, 2);
lean_inc(x_25);
lean_dec(x_19);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_dec(x_28);
lean_ctor_set(x_22, 1, x_25);
lean_ctor_set(x_22, 0, x_24);
lean_inc(x_2);
x_29 = l___private_Lean_Elab_Command_3__setState(x_22, x_2, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_6, x_2, x_30);
lean_dec(x_6);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_22, 2);
x_37 = lean_ctor_get(x_22, 3);
x_38 = lean_ctor_get(x_22, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 4, x_38);
lean_inc(x_2);
x_40 = l___private_Lean_Elab_Command_3__setState(x_39, x_2, x_23);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_6, x_2, x_41);
lean_dec(x_6);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_2);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
return x_20;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_18, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_dec(x_18);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_2);
x_54 = l___private_Lean_Elab_Command_2__getState(x_2, x_15);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_52, 2);
lean_inc(x_59);
lean_dec(x_52);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
lean_ctor_set(x_56, 1, x_59);
lean_ctor_set(x_56, 0, x_58);
x_63 = l___private_Lean_Elab_Command_3__setState(x_56, x_2, x_57);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 0, x_53);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_53);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 0);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_56, 2);
x_73 = lean_ctor_get(x_56, 3);
x_74 = lean_ctor_get(x_56, 4);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_56);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_58);
lean_ctor_set(x_75, 1, x_59);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_73);
lean_ctor_set(x_75, 4, x_74);
x_76 = l___private_Lean_Elab_Command_3__setState(x_75, x_2, x_57);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
 lean_ctor_set_tag(x_79, 1);
}
lean_ctor_set(x_79, 0, x_53);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_53);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_54);
if (x_84 == 0)
{
return x_54;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_54, 0);
x_86 = lean_ctor_get(x_54, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_54);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_18);
x_88 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_89 = l_unreachable_x21___rarg(x_88);
lean_inc(x_2);
x_90 = lean_apply_2(x_89, x_2, x_15);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__2(x_6, x_2, x_91);
lean_dec(x_6);
return x_92;
}
else
{
uint8_t x_93; 
lean_dec(x_6);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_13);
if (x_97 == 0)
{
return x_13;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_13, 0);
x_99 = lean_ctor_get(x_13, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_13);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_9);
if (x_101 == 0)
{
return x_9;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_9, 0);
x_103 = lean_ctor_get(x_9, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_9);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabVariables___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabVariables(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_variables___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withoutModifyingEnv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_5);
x_10 = l_Lean_Elab_Command_setEnv(x_5, x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Elab_Command_setEnv(x_5, x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_15);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = l_Lean_Elab_Command_setEnv(x_5, x_2, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_26);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
return x_4;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Elab_Command_withoutModifyingEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withoutModifyingEnv___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = 1;
lean_inc(x_4);
x_8 = l_Lean_Elab_Term_elabTermAux___main(x_6, x_7, x_7, x_1, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = lean_box(0);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_11, x_12, x_4, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_9);
x_15 = l_Lean_Elab_Term_inferType(x_2, x_9, x_4, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_9);
x_19 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = 0;
x_24 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_2, x_23, x_22, x_4, x_17);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_12);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_check");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabCheck___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCheck___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_inc(x_2);
x_7 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_29; lean_object* x_30; lean_object* x_41; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_2);
x_41 = l___private_Lean_Elab_Command_2__getState(x_2, x_9);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Command_9__getVarDecls(x_42);
lean_dec(x_42);
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Command_2__getState(x_2, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_Command_elabCheck___closed__3;
x_49 = l___private_Lean_Elab_Command_6__mkTermContext(x_2, x_46, x_48);
x_50 = l___private_Lean_Elab_Command_7__mkTermState(x_46);
lean_dec(x_46);
x_51 = l_Lean_Elab_Term_elabBinders___rarg(x_44, x_6, x_49, x_50);
lean_dec(x_44);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_2);
x_54 = l___private_Lean_Elab_Command_2__getState(x_2, x_47);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_53, 2);
lean_inc(x_59);
lean_dec(x_53);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
lean_ctor_set(x_56, 1, x_59);
lean_ctor_set(x_56, 0, x_58);
lean_inc(x_2);
x_63 = l___private_Lean_Elab_Command_3__setState(x_56, x_2, x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_10 = x_52;
x_11 = x_64;
goto block_28;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_52);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_29 = x_65;
x_30 = x_66;
goto block_40;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_56, 2);
x_68 = lean_ctor_get(x_56, 3);
x_69 = lean_ctor_get(x_56, 4);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_68);
lean_ctor_set(x_70, 4, x_69);
lean_inc(x_2);
x_71 = l___private_Lean_Elab_Command_3__setState(x_70, x_2, x_57);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_10 = x_52;
x_11 = x_72;
goto block_28;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_52);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_29 = x_73;
x_30 = x_74;
goto block_40;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_53);
lean_dec(x_52);
x_75 = lean_ctor_get(x_54, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_54, 1);
lean_inc(x_76);
lean_dec(x_54);
x_29 = x_75;
x_30 = x_76;
goto block_40;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_51, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_51, 1);
lean_inc(x_78);
lean_dec(x_51);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_2);
x_80 = l___private_Lean_Elab_Command_2__getState(x_2, x_47);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_ctor_get(x_78, 2);
lean_inc(x_85);
lean_dec(x_78);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
lean_ctor_set(x_82, 1, x_85);
lean_ctor_set(x_82, 0, x_84);
lean_inc(x_2);
x_89 = l___private_Lean_Elab_Command_3__setState(x_82, x_2, x_83);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_29 = x_79;
x_30 = x_90;
goto block_40;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_79);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_29 = x_91;
x_30 = x_92;
goto block_40;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_82, 2);
x_94 = lean_ctor_get(x_82, 3);
x_95 = lean_ctor_get(x_82, 4);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_82);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_85);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
lean_ctor_set(x_96, 4, x_95);
lean_inc(x_2);
x_97 = l___private_Lean_Elab_Command_3__setState(x_96, x_2, x_83);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_29 = x_79;
x_30 = x_98;
goto block_40;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_79);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_29 = x_99;
x_30 = x_100;
goto block_40;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_79);
lean_dec(x_78);
x_101 = lean_ctor_get(x_80, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 1);
lean_inc(x_102);
lean_dec(x_80);
x_29 = x_101;
x_30 = x_102;
goto block_40;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_51);
x_103 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_104 = l_unreachable_x21___rarg(x_103);
lean_inc(x_2);
x_105 = lean_apply_2(x_104, x_2, x_47);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_10 = x_106;
x_11 = x_107;
goto block_28;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_29 = x_108;
x_30 = x_109;
goto block_40;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_44);
lean_dec(x_6);
x_110 = lean_ctor_get(x_45, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_45, 1);
lean_inc(x_111);
lean_dec(x_45);
x_29 = x_110;
x_30 = x_111;
goto block_40;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_6);
x_112 = lean_ctor_get(x_41, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_41, 1);
lean_inc(x_113);
lean_dec(x_41);
x_29 = x_112;
x_30 = x_113;
goto block_40;
}
block_28:
{
lean_object* x_12; 
lean_inc(x_2);
lean_inc(x_8);
x_12 = l_Lean_Elab_Command_setEnv(x_8, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Elab_Command_setEnv(x_8, x_2, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
block_40:
{
lean_object* x_31; 
x_31 = l_Lean_Elab_Command_setEnv(x_8, x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_29);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_6);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_7);
if (x_114 == 0)
{
return x_7;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_7, 0);
x_116 = lean_ctor_get(x_7, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_7);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabCheck___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___closed__2;
x_2 = l_Lean_Meta_check___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_2__getState(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected success");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Exception_hasToString___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
x_9 = l___private_Lean_Elab_Command_2__getState(x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = l_PersistentArray_empty___closed__3;
lean_ctor_set(x_10, 1, x_14);
lean_inc(x_3);
x_15 = l___private_Lean_Elab_Command_3__setState(x_10, x_3, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_56; lean_object* x_57; lean_object* x_98; lean_object* x_99; lean_object* x_134; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_3);
x_134 = lean_apply_2(x_2, x_3, x_16);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
lean_inc(x_3);
x_136 = l_Lean_Elab_Command_hasNoErrorMessages(x_3, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_unbox(x_137);
lean_dec(x_137);
x_56 = x_139;
x_57 = x_138;
goto block_97;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_98 = x_140;
x_99 = x_141;
goto block_133;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_134, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_134, 1);
lean_inc(x_143);
lean_dec(x_134);
x_98 = x_142;
x_99 = x_143;
goto block_133;
}
block_55:
{
lean_object* x_19; 
lean_inc(x_3);
x_19 = l___private_Lean_Elab_Command_2__getState(x_3, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_23);
x_25 = l_PersistentArray_append___rarg(x_8, x_24);
lean_dec(x_24);
lean_ctor_set(x_20, 1, x_25);
x_26 = l___private_Lean_Elab_Command_3__setState(x_20, x_3, x_21);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_17);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
x_37 = lean_ctor_get(x_20, 2);
x_38 = lean_ctor_get(x_20, 3);
x_39 = lean_ctor_get(x_20, 4);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_40 = l_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_36);
x_41 = l_PersistentArray_append___rarg(x_8, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_39);
x_43 = l___private_Lean_Elab_Command_3__setState(x_42, x_3, x_21);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_17);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_17);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
return x_19;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_19);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_97:
{
lean_object* x_58; 
lean_inc(x_3);
x_58 = l___private_Lean_Elab_Command_2__getState(x_3, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_59, 1);
x_63 = l_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_62);
lean_inc(x_8);
x_64 = l_PersistentArray_append___rarg(x_8, x_63);
lean_dec(x_63);
lean_ctor_set(x_59, 1, x_64);
lean_inc(x_3);
x_65 = l___private_Lean_Elab_Command_3__setState(x_59, x_3, x_60);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_8);
if (x_56 == 0)
{
uint8_t x_66; 
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_65, 0, x_68);
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_dec(x_65);
x_73 = l_Lean_Elab_Command_failIfSucceeds___closed__3;
x_74 = l_Lean_Elab_Command_throwError___rarg(x_1, x_73, x_3, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
lean_dec(x_65);
x_17 = x_75;
x_18 = x_76;
goto block_55;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_59, 0);
x_78 = lean_ctor_get(x_59, 1);
x_79 = lean_ctor_get(x_59, 2);
x_80 = lean_ctor_get(x_59, 3);
x_81 = lean_ctor_get(x_59, 4);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_59);
x_82 = l_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_78);
lean_inc(x_8);
x_83 = l_PersistentArray_append___rarg(x_8, x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_80);
lean_ctor_set(x_84, 4, x_81);
lean_inc(x_3);
x_85 = l___private_Lean_Elab_Command_3__setState(x_84, x_3, x_60);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_8);
if (x_56 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = l_Lean_Elab_Command_failIfSucceeds___closed__3;
x_92 = l_Lean_Elab_Command_throwError___rarg(x_1, x_91, x_3, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
lean_dec(x_85);
x_17 = x_93;
x_18 = x_94;
goto block_55;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_58, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_58, 1);
lean_inc(x_96);
lean_dec(x_58);
x_17 = x_95;
x_18 = x_96;
goto block_55;
}
}
block_133:
{
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_3);
x_101 = l___private_Lean_Elab_Command_2__getState(x_3, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_102, 1);
x_106 = l_PersistentArray_push___rarg(x_105, x_100);
lean_ctor_set(x_102, 1, x_106);
lean_inc(x_3);
x_107 = l___private_Lean_Elab_Command_3__setState(x_102, x_3, x_103);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = 0;
x_56 = x_109;
x_57 = x_108;
goto block_97;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_17 = x_110;
x_18 = x_111;
goto block_55;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_102, 0);
x_113 = lean_ctor_get(x_102, 1);
x_114 = lean_ctor_get(x_102, 2);
x_115 = lean_ctor_get(x_102, 3);
x_116 = lean_ctor_get(x_102, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_102);
x_117 = l_PersistentArray_push___rarg(x_113, x_100);
x_118 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_114);
lean_ctor_set(x_118, 3, x_115);
lean_ctor_set(x_118, 4, x_116);
lean_inc(x_3);
x_119 = l___private_Lean_Elab_Command_3__setState(x_118, x_3, x_103);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = 0;
x_56 = x_121;
x_57 = x_120;
goto block_97;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_dec(x_119);
x_17 = x_122;
x_18 = x_123;
goto block_55;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_100);
x_124 = lean_ctor_get(x_101, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_101, 1);
lean_inc(x_125);
lean_dec(x_101);
x_17 = x_124;
x_18 = x_125;
goto block_55;
}
}
else
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_126 = 2;
x_127 = l_Lean_Elab_Command_failIfSucceeds___closed__5;
lean_inc(x_3);
x_128 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_126, x_127, x_3, x_99);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = 0;
x_56 = x_130;
x_57 = x_129;
goto block_97;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_17 = x_131;
x_18 = x_132;
goto block_55;
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_15);
if (x_144 == 0)
{
return x_15;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_15, 0);
x_146 = lean_ctor_get(x_15, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_15);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_10, 0);
x_149 = lean_ctor_get(x_10, 2);
x_150 = lean_ctor_get(x_10, 3);
x_151 = lean_ctor_get(x_10, 4);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_10);
x_152 = l_PersistentArray_empty___closed__3;
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_149);
lean_ctor_set(x_153, 3, x_150);
lean_ctor_set(x_153, 4, x_151);
lean_inc(x_3);
x_154 = l___private_Lean_Elab_Command_3__setState(x_153, x_3, x_11);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_183; lean_object* x_184; lean_object* x_210; lean_object* x_211; lean_object* x_239; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
lean_inc(x_3);
x_239 = lean_apply_2(x_2, x_3, x_155);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
lean_inc(x_3);
x_241 = l_Lean_Elab_Command_hasNoErrorMessages(x_3, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unbox(x_242);
lean_dec(x_242);
x_183 = x_244;
x_184 = x_243;
goto block_209;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 1);
lean_inc(x_246);
lean_dec(x_241);
x_210 = x_245;
x_211 = x_246;
goto block_238;
}
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_239, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_239, 1);
lean_inc(x_248);
lean_dec(x_239);
x_210 = x_247;
x_211 = x_248;
goto block_238;
}
block_182:
{
lean_object* x_158; 
lean_inc(x_3);
x_158 = l___private_Lean_Elab_Command_2__getState(x_3, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_159, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 lean_ctor_release(x_159, 2);
 lean_ctor_release(x_159, 3);
 lean_ctor_release(x_159, 4);
 x_166 = x_159;
} else {
 lean_dec_ref(x_159);
 x_166 = lean_box(0);
}
x_167 = l_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_162);
x_168 = l_PersistentArray_append___rarg(x_8, x_167);
lean_dec(x_167);
if (lean_is_scalar(x_166)) {
 x_169 = lean_alloc_ctor(0, 5, 0);
} else {
 x_169 = x_166;
}
lean_ctor_set(x_169, 0, x_161);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_163);
lean_ctor_set(x_169, 3, x_164);
lean_ctor_set(x_169, 4, x_165);
x_170 = l___private_Lean_Elab_Command_3__setState(x_169, x_3, x_160);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_156);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_156);
x_174 = lean_ctor_get(x_170, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_176 = x_170;
} else {
 lean_dec_ref(x_170);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_156);
lean_dec(x_8);
lean_dec(x_3);
x_178 = lean_ctor_get(x_158, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_158, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_180 = x_158;
} else {
 lean_dec_ref(x_158);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
block_209:
{
lean_object* x_185; 
lean_inc(x_3);
x_185 = l___private_Lean_Elab_Command_2__getState(x_3, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 4);
lean_inc(x_192);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 x_193 = x_186;
} else {
 lean_dec_ref(x_186);
 x_193 = lean_box(0);
}
x_194 = l_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_189);
lean_inc(x_8);
x_195 = l_PersistentArray_append___rarg(x_8, x_194);
lean_dec(x_194);
if (lean_is_scalar(x_193)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_193;
}
lean_ctor_set(x_196, 0, x_188);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_196, 2, x_190);
lean_ctor_set(x_196, 3, x_191);
lean_ctor_set(x_196, 4, x_192);
lean_inc(x_3);
x_197 = l___private_Lean_Elab_Command_3__setState(x_196, x_3, x_187);
if (lean_obj_tag(x_197) == 0)
{
lean_dec(x_8);
if (x_183 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_3);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_box(0);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = l_Lean_Elab_Command_failIfSucceeds___closed__3;
x_204 = l_Lean_Elab_Command_throwError___rarg(x_1, x_203, x_3, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_197, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_197, 1);
lean_inc(x_206);
lean_dec(x_197);
x_156 = x_205;
x_157 = x_206;
goto block_182;
}
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_185, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_185, 1);
lean_inc(x_208);
lean_dec(x_185);
x_156 = x_207;
x_157 = x_208;
goto block_182;
}
}
block_238:
{
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_3);
x_213 = l___private_Lean_Elab_Command_2__getState(x_3, x_211);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_214, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 4);
lean_inc(x_220);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 x_221 = x_214;
} else {
 lean_dec_ref(x_214);
 x_221 = lean_box(0);
}
x_222 = l_PersistentArray_push___rarg(x_217, x_212);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(0, 5, 0);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_216);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_218);
lean_ctor_set(x_223, 3, x_219);
lean_ctor_set(x_223, 4, x_220);
lean_inc(x_3);
x_224 = l___private_Lean_Elab_Command_3__setState(x_223, x_3, x_215);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = 0;
x_183 = x_226;
x_184 = x_225;
goto block_209;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
lean_dec(x_224);
x_156 = x_227;
x_157 = x_228;
goto block_182;
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_212);
x_229 = lean_ctor_get(x_213, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_213, 1);
lean_inc(x_230);
lean_dec(x_213);
x_156 = x_229;
x_157 = x_230;
goto block_182;
}
}
else
{
uint8_t x_231; lean_object* x_232; lean_object* x_233; 
x_231 = 2;
x_232 = l_Lean_Elab_Command_failIfSucceeds___closed__5;
lean_inc(x_3);
x_233 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_231, x_232, x_3, x_211);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = 0;
x_183 = x_235;
x_184 = x_234;
goto block_209;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
lean_dec(x_233);
x_156 = x_236;
x_157 = x_237;
goto block_182;
}
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_249 = lean_ctor_get(x_154, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_154, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_251 = x_154;
} else {
 lean_dec_ref(x_154);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_253 = !lean_is_exclusive(x_9);
if (x_253 == 0)
{
return x_9;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_9, 0);
x_255 = lean_ctor_get(x_9, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_9);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_3);
lean_dec(x_2);
x_257 = !lean_is_exclusive(x_5);
if (x_257 == 0)
{
return x_5;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_5, 0);
x_259 = lean_ctor_get(x_5, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_5);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_failIfSucceeds(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabCheckFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Command_failIfSucceeds(x_1, x_4, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckFailure), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_check__failure___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = l___private_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_Command_6__mkTermContext(x_3, x_7, x_5);
x_10 = l___private_Lean_Elab_Command_7__mkTermState(x_7);
lean_dec(x_7);
x_11 = l_Lean_Elab_Term_addDecl(x_1, x_2, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = l___private_Lean_Elab_Command_2__getState(x_3, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_13, 2);
lean_inc(x_19);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
lean_ctor_set(x_16, 1, x_19);
lean_ctor_set(x_16, 0, x_18);
x_23 = l___private_Lean_Elab_Command_3__setState(x_16, x_3, x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_12);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_16, 2);
x_33 = lean_ctor_get(x_16, 3);
x_34 = lean_ctor_get(x_16, 4);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_19);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
x_36 = l___private_Lean_Elab_Command_3__setState(x_35, x_3, x_17);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_12);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_42 = x_36;
} else {
 lean_dec_ref(x_36);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_11, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
lean_dec(x_11);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_3);
x_51 = l___private_Lean_Elab_Command_2__getState(x_3, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_49, 2);
lean_inc(x_56);
lean_dec(x_49);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_53, 0);
lean_dec(x_59);
lean_ctor_set(x_53, 1, x_56);
lean_ctor_set(x_53, 0, x_55);
x_60 = l___private_Lean_Elab_Command_3__setState(x_53, x_3, x_54);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_50);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
x_71 = lean_ctor_get(x_53, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_53);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_55);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
x_73 = l___private_Lean_Elab_Command_3__setState(x_72, x_3, x_54);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_50);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_50);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_51);
if (x_81 == 0)
{
return x_51;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_51, 0);
x_83 = lean_ctor_get(x_51, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_51);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
return x_6;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_6);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
lean_object* l_Lean_Elab_Command_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_compileDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = l___private_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_Command_6__mkTermContext(x_3, x_7, x_5);
x_10 = l___private_Lean_Elab_Command_7__mkTermState(x_7);
lean_dec(x_7);
x_11 = l_Lean_Elab_Term_compileDecl(x_1, x_2, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = l___private_Lean_Elab_Command_2__getState(x_3, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_13, 2);
lean_inc(x_19);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
lean_ctor_set(x_16, 1, x_19);
lean_ctor_set(x_16, 0, x_18);
x_23 = l___private_Lean_Elab_Command_3__setState(x_16, x_3, x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_12);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_16, 2);
x_33 = lean_ctor_get(x_16, 3);
x_34 = lean_ctor_get(x_16, 4);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_19);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
x_36 = l___private_Lean_Elab_Command_3__setState(x_35, x_3, x_17);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_12);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_42 = x_36;
} else {
 lean_dec_ref(x_36);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_11, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
lean_dec(x_11);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_3);
x_51 = l___private_Lean_Elab_Command_2__getState(x_3, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_49, 2);
lean_inc(x_56);
lean_dec(x_49);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_53, 0);
lean_dec(x_59);
lean_ctor_set(x_53, 1, x_56);
lean_ctor_set(x_53, 0, x_55);
x_60 = l___private_Lean_Elab_Command_3__setState(x_53, x_3, x_54);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_50);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
x_71 = lean_ctor_get(x_53, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_53);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_55);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
x_73 = l___private_Lean_Elab_Command_3__setState(x_72, x_3, x_54);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_50);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_50);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_51);
if (x_81 == 0)
{
return x_51;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_51, 0);
x_83 = lean_ctor_get(x_51, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_51);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
return x_6;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_6);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
lean_object* l_Lean_Elab_Command_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_compileDecl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isSyntheticSorry___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__1;
x_2 = l_Bool_HasRepr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Parser_Command_eval___elambda__1___closed__1;
x_10 = lean_name_mk_string(x_1, x_9);
x_11 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__2;
x_12 = l_Lean_mkConst(x_11, x_2);
x_13 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_inc(x_3);
x_14 = lean_array_push(x_13, x_3);
lean_inc(x_6);
x_15 = lean_array_push(x_14, x_6);
x_16 = lean_array_push(x_15, x_4);
x_17 = lean_array_push(x_16, x_12);
lean_inc(x_7);
x_18 = l_Lean_Elab_Term_mkAppM(x_5, x_10, x_17, x_7, x_8);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_mkAppStx___closed__9;
x_22 = lean_array_push(x_21, x_3);
x_23 = lean_array_push(x_22, x_6);
x_24 = l_Lean_Elab_Term_mkLambda(x_5, x_23, x_19, x_7, x_20);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("opts");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Options");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__3;
x_10 = lean_name_mk_string(x_1, x_9);
lean_inc(x_2);
x_11 = l_Lean_mkConst(x_10, x_2);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed), 8, 5);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_6);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
x_13 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2;
x_14 = 0;
x_15 = l_Lean_Elab_Term_withLocalDecl___rarg(x_5, x_13, x_14, x_11, x_12, x_7, x_8);
lean_dec(x_5);
return x_15;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MetaHasEval");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasEval");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__4;
x_2 = l_Lean_Parser_Command_eval___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("env");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Environment");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__10;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = 1;
lean_inc(x_6);
x_10 = l_Lean_Elab_Term_elabTermAux___main(x_8, x_9, x_9, x_1, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2;
x_14 = l_Lean_Environment_contains(x_2, x_13);
x_133 = 0;
x_134 = lean_box(0);
lean_inc(x_6);
x_135 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_133, x_134, x_6, x_12);
if (x_14 == 0)
{
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_15 = x_133;
x_16 = x_136;
goto block_132;
}
else
{
uint8_t x_137; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_135, 0);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_135);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
lean_dec(x_135);
x_15 = x_9;
x_16 = x_141;
goto block_132;
}
else
{
uint8_t x_142; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_142 = !lean_is_exclusive(x_135);
if (x_142 == 0)
{
return x_135;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_135, 0);
x_144 = lean_ctor_get(x_135, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_135);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
block_132:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_box(0);
x_18 = l_Lean_mkAppStx___closed__9;
x_19 = lean_array_push(x_18, x_11);
x_20 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__6;
x_21 = lean_array_push(x_19, x_20);
x_22 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__5;
lean_inc(x_6);
x_23 = l_Lean_Elab_Term_mkAppM(x_3, x_22, x_21, x_6, x_16);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_24);
x_26 = l_Lean_Elab_Term_inferType(x_3, x_24, x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_4);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_9);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_6);
x_33 = l_Lean_Elab_Term_addDecl(x_3, x_32, x_6, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_6);
x_35 = l_Lean_Elab_Term_compileDecl(x_3, x_32, x_6, x_34);
lean_dec(x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Term_getEnv___rarg(x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_eval_const(x_39, x_4);
lean_dec(x_4);
lean_dec(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_Elab_Term_throwError___rarg(x_3, x_44, x_6, x_40);
lean_dec(x_3);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_3);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
x_49 = lean_eval_const(x_47, x_4);
lean_dec(x_4);
lean_dec(x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_Elab_Term_throwError___rarg(x_3, x_52, x_6, x_48);
lean_dec(x_3);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_3);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
return x_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_35, 0);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_33);
if (x_60 == 0)
{
return x_33;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_33, 0);
x_62 = lean_ctor_get(x_33, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_33);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_26);
if (x_64 == 0)
{
return x_26;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_26, 0);
x_66 = lean_ctor_get(x_26, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_23);
if (x_68 == 0)
{
return x_23;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_23, 0);
x_70 = lean_ctor_get(x_23, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_23);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_box(0);
x_73 = l_Lean_mkAppStx___closed__2;
lean_inc(x_3);
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2), 8, 5);
lean_closure_set(x_74, 0, x_73);
lean_closure_set(x_74, 1, x_72);
lean_closure_set(x_74, 2, x_13);
lean_closure_set(x_74, 3, x_11);
lean_closure_set(x_74, 4, x_3);
x_75 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__8;
x_76 = 0;
x_77 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__11;
lean_inc(x_6);
x_78 = l_Lean_Elab_Term_withLocalDecl___rarg(x_3, x_75, x_76, x_77, x_74, x_6, x_16);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_6);
lean_inc(x_79);
x_81 = l_Lean_Elab_Term_inferType(x_3, x_79, x_6, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_4);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_4);
lean_ctor_set(x_84, 1, x_72);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_79);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_9);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_inc(x_6);
x_88 = l_Lean_Elab_Term_addDecl(x_3, x_87, x_6, x_83);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_6);
x_90 = l_Lean_Elab_Term_compileDecl(x_3, x_87, x_6, x_89);
lean_dec(x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_Elab_Term_getEnv___rarg(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Elab_Term_getOptions(x_6, x_94);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = lean_eval_const(x_93, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_95);
lean_dec(x_97);
lean_dec(x_93);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lean_Elab_Term_throwError___rarg(x_3, x_102, x_6, x_98);
lean_dec(x_3);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_6);
lean_dec(x_3);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_apply_2(x_104, x_93, x_97);
lean_ctor_set(x_95, 0, x_105);
return x_95;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_95, 0);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_95);
x_108 = lean_eval_const(x_93, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_106);
lean_dec(x_93);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_Elab_Term_throwError___rarg(x_3, x_111, x_6, x_107);
lean_dec(x_3);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_6);
lean_dec(x_3);
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_apply_2(x_113, x_93, x_106);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_107);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_90);
if (x_116 == 0)
{
return x_90;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_90, 0);
x_118 = lean_ctor_get(x_90, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_90);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_87);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_120 = !lean_is_exclusive(x_88);
if (x_120 == 0)
{
return x_88;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_88, 0);
x_122 = lean_ctor_get(x_88, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_88);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_81);
if (x_124 == 0)
{
return x_81;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_81, 0);
x_126 = lean_ctor_get(x_81, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_81);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_128 = !lean_is_exclusive(x_78);
if (x_128 == 0)
{
return x_78;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_78, 0);
x_130 = lean_ctor_get(x_78, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_78);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_10);
if (x_146 == 0)
{
return x_10;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_10, 0);
x_148 = lean_ctor_get(x_10, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_10);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_eval");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_21; lean_object* x_22; lean_object* x_62; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_62 = l_Lean_Elab_Command_getEnv(x_2, x_8);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
lean_inc(x_1);
x_66 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed), 7, 4);
lean_closure_set(x_66, 0, x_5);
lean_closure_set(x_66, 1, x_63);
lean_closure_set(x_66, 2, x_1);
lean_closure_set(x_66, 3, x_65);
lean_inc(x_2);
x_67 = l___private_Lean_Elab_Command_2__getState(x_2, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l___private_Lean_Elab_Command_9__getVarDecls(x_68);
lean_dec(x_68);
lean_inc(x_2);
x_71 = l___private_Lean_Elab_Command_2__getState(x_2, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
x_75 = l___private_Lean_Elab_Command_6__mkTermContext(x_2, x_72, x_74);
x_76 = l___private_Lean_Elab_Command_7__mkTermState(x_72);
lean_dec(x_72);
x_77 = l_Lean_Elab_Term_elabBinders___rarg(x_70, x_66, x_75, x_76);
lean_dec(x_70);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_2);
x_80 = l___private_Lean_Elab_Command_2__getState(x_2, x_73);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_ctor_get(x_79, 2);
lean_inc(x_85);
lean_dec(x_79);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
lean_ctor_set(x_82, 1, x_85);
lean_ctor_set(x_82, 0, x_84);
lean_inc(x_2);
x_89 = l___private_Lean_Elab_Command_3__setState(x_82, x_2, x_83);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_21 = x_78;
x_22 = x_90;
goto block_61;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_78);
lean_dec(x_1);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_9 = x_91;
x_10 = x_92;
goto block_20;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_82, 2);
x_94 = lean_ctor_get(x_82, 3);
x_95 = lean_ctor_get(x_82, 4);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_82);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_85);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
lean_ctor_set(x_96, 4, x_95);
lean_inc(x_2);
x_97 = l___private_Lean_Elab_Command_3__setState(x_96, x_2, x_83);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_21 = x_78;
x_22 = x_98;
goto block_61;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_78);
lean_dec(x_1);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_9 = x_99;
x_10 = x_100;
goto block_20;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_1);
x_101 = lean_ctor_get(x_80, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 1);
lean_inc(x_102);
lean_dec(x_80);
x_9 = x_101;
x_10 = x_102;
goto block_20;
}
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_77, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_1);
x_104 = lean_ctor_get(x_77, 1);
lean_inc(x_104);
lean_dec(x_77);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_2);
x_106 = l___private_Lean_Elab_Command_2__getState(x_2, x_73);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_ctor_get(x_104, 2);
lean_inc(x_111);
lean_dec(x_104);
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 1);
lean_dec(x_113);
x_114 = lean_ctor_get(x_108, 0);
lean_dec(x_114);
lean_ctor_set(x_108, 1, x_111);
lean_ctor_set(x_108, 0, x_110);
lean_inc(x_2);
x_115 = l___private_Lean_Elab_Command_3__setState(x_108, x_2, x_109);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_9 = x_105;
x_10 = x_116;
goto block_20;
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_105);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_9 = x_117;
x_10 = x_118;
goto block_20;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_108, 2);
x_120 = lean_ctor_get(x_108, 3);
x_121 = lean_ctor_get(x_108, 4);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_108);
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_110);
lean_ctor_set(x_122, 1, x_111);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_121);
lean_inc(x_2);
x_123 = l___private_Lean_Elab_Command_3__setState(x_122, x_2, x_109);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_9 = x_105;
x_10 = x_124;
goto block_20;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_105);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_9 = x_125;
x_10 = x_126;
goto block_20;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_105);
lean_dec(x_104);
x_127 = lean_ctor_get(x_106, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_106, 1);
lean_inc(x_128);
lean_dec(x_106);
x_9 = x_127;
x_10 = x_128;
goto block_20;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_77);
x_129 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_130 = l_unreachable_x21___rarg(x_129);
lean_inc(x_2);
x_131 = lean_apply_2(x_130, x_2, x_73);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_21 = x_132;
x_22 = x_133;
goto block_61;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_1);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_9 = x_134;
x_10 = x_135;
goto block_20;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_1);
x_136 = lean_ctor_get(x_71, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_71, 1);
lean_inc(x_137);
lean_dec(x_71);
x_9 = x_136;
x_10 = x_137;
goto block_20;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_66);
lean_dec(x_1);
x_138 = lean_ctor_get(x_67, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_67, 1);
lean_inc(x_139);
lean_dec(x_67);
x_9 = x_138;
x_10 = x_139;
goto block_20;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_5);
lean_dec(x_1);
x_140 = lean_ctor_get(x_62, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_62, 1);
lean_inc(x_141);
lean_dec(x_62);
x_9 = x_140;
x_10 = x_141;
goto block_20;
}
block_20:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_setEnv(x_7, x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
block_61:
{
lean_object* x_23; 
x_23 = lean_with_isolated_streams(x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = 0;
lean_inc(x_2);
x_31 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_30, x_29, x_2, x_25);
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
lean_inc(x_2);
x_34 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_2, x_1, x_33);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_9 = x_35;
x_10 = x_32;
goto block_20;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
lean_dec(x_1);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
lean_inc(x_2);
lean_inc(x_7);
x_37 = l_Lean_Elab_Command_setEnv(x_7, x_2, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_dec(x_37);
x_46 = l_Lean_Elab_Command_setEnv(x_7, x_2, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_44);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_44);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_27);
lean_dec(x_1);
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_dec(x_31);
x_9 = x_55;
x_10 = x_56;
goto block_20;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_23, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_dec(x_23);
lean_inc(x_2);
x_59 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_2, x_1, x_57);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_9 = x_60;
x_10 = x_58;
goto block_20;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_6);
if (x_142 == 0)
{
return x_6;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_6, 0);
x_144 = lean_ctor_get(x_6, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_6);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabEval___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Exception_inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabEval(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEval___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabEval___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_elabEval(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_eval___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = 1;
lean_inc(x_4);
x_8 = l_Lean_Elab_Term_elabTermAux___main(x_6, x_7, x_7, x_1, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = lean_box(0);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_11, x_12, x_4, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_4);
x_15 = l_Lean_Elab_Term_instantiateMVars(x_2, x_9, x_4, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 4);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_17, 4, x_22);
x_23 = l_Lean_Meta_synthInstance(x_18, x_21, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_4);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_25, x_20);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = 0;
x_29 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_2, x_28, x_27, x_4, x_26);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_12);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_4);
x_37 = l___private_Lean_Elab_Term_2__fromMetaException(x_4, x_2, x_35);
x_38 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_36, x_20);
lean_ctor_set(x_23, 1, x_38);
lean_ctor_set(x_23, 0, x_37);
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
lean_inc(x_4);
x_41 = l___private_Lean_Elab_Term_2__fromMetaException(x_4, x_2, x_39);
x_42 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_40, x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
x_46 = lean_ctor_get(x_17, 2);
x_47 = lean_ctor_get(x_17, 3);
x_48 = lean_ctor_get(x_17, 4);
x_49 = lean_ctor_get(x_17, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
x_51 = l_Lean_TraceState_Inhabited___closed__1;
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_49);
x_53 = l_Lean_Meta_synthInstance(x_18, x_50, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_4);
x_56 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_55, x_48);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_58 = 0;
x_59 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_2, x_58, x_57, x_4, x_56);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_65 = x_53;
} else {
 lean_dec_ref(x_53);
 x_65 = lean_box(0);
}
lean_inc(x_4);
x_66 = l___private_Lean_Elab_Term_2__fromMetaException(x_4, x_2, x_63);
x_67 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_64, x_48);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_9);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_13);
if (x_69 == 0)
{
return x_13;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_13, 0);
x_71 = lean_ctor_get(x_13, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_13);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_8);
if (x_73 == 0)
{
return x_8;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_8, 0);
x_75 = lean_ctor_get(x_8, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_8);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_synth_cmd");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSynth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSynth___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSynth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_inc(x_2);
x_7 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_29; lean_object* x_30; lean_object* x_41; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_2);
x_41 = l___private_Lean_Elab_Command_2__getState(x_2, x_9);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Command_9__getVarDecls(x_42);
lean_dec(x_42);
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Command_2__getState(x_2, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_Command_elabSynth___closed__3;
x_49 = l___private_Lean_Elab_Command_6__mkTermContext(x_2, x_46, x_48);
x_50 = l___private_Lean_Elab_Command_7__mkTermState(x_46);
lean_dec(x_46);
x_51 = l_Lean_Elab_Term_elabBinders___rarg(x_44, x_6, x_49, x_50);
lean_dec(x_44);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_2);
x_54 = l___private_Lean_Elab_Command_2__getState(x_2, x_47);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_53, 2);
lean_inc(x_59);
lean_dec(x_53);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
lean_ctor_set(x_56, 1, x_59);
lean_ctor_set(x_56, 0, x_58);
lean_inc(x_2);
x_63 = l___private_Lean_Elab_Command_3__setState(x_56, x_2, x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_10 = x_52;
x_11 = x_64;
goto block_28;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_52);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_29 = x_65;
x_30 = x_66;
goto block_40;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_56, 2);
x_68 = lean_ctor_get(x_56, 3);
x_69 = lean_ctor_get(x_56, 4);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_68);
lean_ctor_set(x_70, 4, x_69);
lean_inc(x_2);
x_71 = l___private_Lean_Elab_Command_3__setState(x_70, x_2, x_57);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_10 = x_52;
x_11 = x_72;
goto block_28;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_52);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_29 = x_73;
x_30 = x_74;
goto block_40;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_53);
lean_dec(x_52);
x_75 = lean_ctor_get(x_54, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_54, 1);
lean_inc(x_76);
lean_dec(x_54);
x_29 = x_75;
x_30 = x_76;
goto block_40;
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_51, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_51, 1);
lean_inc(x_78);
lean_dec(x_51);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_2);
x_80 = l___private_Lean_Elab_Command_2__getState(x_2, x_47);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_ctor_get(x_78, 2);
lean_inc(x_85);
lean_dec(x_78);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
lean_ctor_set(x_82, 1, x_85);
lean_ctor_set(x_82, 0, x_84);
lean_inc(x_2);
x_89 = l___private_Lean_Elab_Command_3__setState(x_82, x_2, x_83);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_29 = x_79;
x_30 = x_90;
goto block_40;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_79);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_29 = x_91;
x_30 = x_92;
goto block_40;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_82, 2);
x_94 = lean_ctor_get(x_82, 3);
x_95 = lean_ctor_get(x_82, 4);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_82);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_85);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
lean_ctor_set(x_96, 4, x_95);
lean_inc(x_2);
x_97 = l___private_Lean_Elab_Command_3__setState(x_96, x_2, x_83);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_29 = x_79;
x_30 = x_98;
goto block_40;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_79);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_29 = x_99;
x_30 = x_100;
goto block_40;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_79);
lean_dec(x_78);
x_101 = lean_ctor_get(x_80, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 1);
lean_inc(x_102);
lean_dec(x_80);
x_29 = x_101;
x_30 = x_102;
goto block_40;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_51);
x_103 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_104 = l_unreachable_x21___rarg(x_103);
lean_inc(x_2);
x_105 = lean_apply_2(x_104, x_2, x_47);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_10 = x_106;
x_11 = x_107;
goto block_28;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_29 = x_108;
x_30 = x_109;
goto block_40;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_44);
lean_dec(x_6);
x_110 = lean_ctor_get(x_45, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_45, 1);
lean_inc(x_111);
lean_dec(x_45);
x_29 = x_110;
x_30 = x_111;
goto block_40;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_6);
x_112 = lean_ctor_get(x_41, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_41, 1);
lean_inc(x_113);
lean_dec(x_41);
x_29 = x_112;
x_30 = x_113;
goto block_40;
}
block_28:
{
lean_object* x_12; 
lean_inc(x_2);
lean_inc(x_8);
x_12 = l_Lean_Elab_Command_setEnv(x_8, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Elab_Command_setEnv(x_8, x_2, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
block_40:
{
lean_object* x_31; 
x_31 = l_Lean_Elab_Command_setEnv(x_8, x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_29);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_6);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_7);
if (x_114 == 0)
{
return x_7;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_7, 0);
x_116 = lean_ctor_get(x_7, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_7);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabSynth___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_synth___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = l_Lean_Elab_Command_modifyScope___closed__1;
x_12 = l_unreachable_x21___rarg(x_11);
lean_ctor_set(x_6, 2, x_12);
x_13 = l___private_Lean_Elab_Command_3__setState(x_6, x_3, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
x_26 = lean_ctor_get(x_6, 3);
x_27 = lean_ctor_get(x_6, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_27);
x_31 = l___private_Lean_Elab_Command_3__setState(x_30, x_3, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 2);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_7, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 2);
x_48 = l_Lean_KVMap_insertCore___main(x_47, x_1, x_2);
lean_ctor_set(x_40, 2, x_48);
x_49 = l___private_Lean_Elab_Command_3__setState(x_6, x_3, x_41);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
x_62 = lean_ctor_get(x_40, 2);
x_63 = lean_ctor_get(x_40, 3);
x_64 = lean_ctor_get(x_40, 4);
x_65 = lean_ctor_get(x_40, 5);
x_66 = lean_ctor_get(x_40, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_67 = l_Lean_KVMap_insertCore___main(x_62, x_1, x_2);
x_68 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_7, 0, x_68);
x_69 = l___private_Lean_Elab_Command_3__setState(x_6, x_3, x_41);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
lean_dec(x_7);
x_79 = lean_ctor_get(x_40, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_40, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_40, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_40, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_40, 6);
lean_inc(x_85);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_86 = x_40;
} else {
 lean_dec_ref(x_40);
 x_86 = lean_box(0);
}
x_87 = l_Lean_KVMap_insertCore___main(x_81, x_1, x_2);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 7, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_87);
lean_ctor_set(x_88, 3, x_82);
lean_ctor_set(x_88, 4, x_83);
lean_ctor_set(x_88, 5, x_84);
lean_ctor_set(x_88, 6, x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_78);
lean_ctor_set(x_6, 2, x_89);
x_90 = l___private_Lean_Elab_Command_3__setState(x_6, x_3, x_41);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_99 = lean_ctor_get(x_6, 0);
x_100 = lean_ctor_get(x_6, 1);
x_101 = lean_ctor_get(x_6, 3);
x_102 = lean_ctor_get(x_6, 4);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_6);
x_103 = lean_ctor_get(x_7, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_104 = x_7;
} else {
 lean_dec_ref(x_7);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_40, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_40, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_40, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 5);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 6);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = l_Lean_KVMap_insertCore___main(x_107, x_1, x_2);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 7, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_108);
lean_ctor_set(x_114, 4, x_109);
lean_ctor_set(x_114, 5, x_110);
lean_ctor_set(x_114, 6, x_111);
if (lean_is_scalar(x_104)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_104;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_103);
x_116 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_100);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set(x_116, 3, x_101);
lean_ctor_set(x_116, 4, x_102);
x_117 = l___private_Lean_Elab_Command_3__setState(x_116, x_3, x_41);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_5);
if (x_126 == 0)
{
return x_5;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_5, 0);
x_128 = lean_ctor_get(x_5, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_5);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_setOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type mismatch at set_option");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_setOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_setOption___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_setOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_setOption___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_setOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_getOptionDecl(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_DataValue_sameCtor(x_9, x_3);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_3);
lean_dec(x_2);
x_105 = l_Lean_Elab_Command_setOption___closed__3;
x_106 = l_Lean_Elab_Command_throwError___rarg(x_1, x_105, x_4, x_8);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
return x_106;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
x_11 = x_8;
goto block_104;
}
block_104:
{
lean_object* x_12; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_getMaxRecDepth___closed__1;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_box(0);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_12);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec(x_3);
lean_inc(x_4);
x_22 = l___private_Lean_Elab_Command_2__getState(x_4, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 4);
lean_dec(x_26);
lean_ctor_set(x_23, 4, x_21);
x_27 = l___private_Lean_Elab_Command_3__setState(x_23, x_4, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
x_40 = lean_ctor_get(x_23, 2);
x_41 = lean_ctor_get(x_23, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_21);
x_43 = l___private_Lean_Elab_Command_3__setState(x_42, x_4, x_24);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_21);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_22);
if (x_52 == 0)
{
return x_22;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_22, 0);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_22);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_4);
lean_dec(x_3);
x_56 = lean_box(0);
lean_ctor_set(x_12, 0, x_56);
return x_12;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_dec(x_12);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_dec(x_2);
x_59 = l_Lean_getMaxRecDepth___closed__1;
x_60 = lean_string_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
else
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
lean_dec(x_3);
lean_inc(x_4);
x_64 = l___private_Lean_Elab_Command_2__getState(x_4, x_57);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 5, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_63);
x_73 = l___private_Lean_Elab_Command_3__setState(x_72, x_4, x_66);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_63);
lean_dec(x_4);
x_82 = lean_ctor_get(x_64, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_64, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_84 = x_64;
} else {
 lean_dec_ref(x_64);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_4);
lean_dec(x_3);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_57);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_12);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_12, 0);
lean_dec(x_89);
x_90 = lean_box(0);
lean_ctor_set(x_12, 0, x_90);
return x_12;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_12, 1);
lean_inc(x_91);
lean_dec(x_12);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_12);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_12, 0);
lean_dec(x_95);
x_96 = lean_box(0);
lean_ctor_set(x_12, 0, x_96);
return x_12;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_12, 1);
lean_inc(x_97);
lean_dec(x_12);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_12);
if (x_100 == 0)
{
return x_12;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_12, 0);
x_102 = lean_ctor_get(x_12, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_12);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_3);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_6);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_6, 0);
x_113 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_4, x_1, x_112);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_6, 0, x_114);
return x_6;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_6, 0);
x_116 = lean_ctor_get(x_6, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_6);
x_117 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_4, x_1, x_115);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
}
}
}
lean_object* l_Lean_Elab_Command_setOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_setOption(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected set_option value ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSetOption___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSetOption___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_22; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getIdAt(x_1, x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_22 = l_Lean_Syntax_isStrLit_x3f(x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_numLitKind;
x_24 = l_Lean_Syntax_isNatLitAux(x_23, x_7);
if (lean_obj_tag(x_24) == 0)
{
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
x_26 = l_Bool_HasRepr___closed__2;
x_27 = lean_string_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Bool_HasRepr___closed__1;
x_29 = lean_string_dec_eq(x_25, x_28);
lean_dec(x_25);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_5);
x_30 = lean_box(0);
x_8 = x_30;
goto block_21;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
x_31 = l_Lean_registerTraceClass___closed__1;
x_32 = l_Lean_Elab_Command_setOption(x_1, x_5, x_31, x_2, x_3);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
lean_dec(x_7);
x_33 = l_Lean_verboseOption___closed__3;
x_34 = l_Lean_Elab_Command_setOption(x_1, x_5, x_33, x_2, x_3);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_5);
x_35 = lean_box(0);
x_8 = x_35;
goto block_21;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_7);
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Elab_Command_setOption(x_1, x_5, x_37, x_2, x_3);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_7);
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_Elab_Command_setOption(x_1, x_5, x_40, x_2, x_3);
return x_41;
}
block_21:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = 0;
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
x_12 = l_Lean_Syntax_formatStxAux___main(x_9, x_10, x_11, x_7);
x_13 = l_Lean_Options_empty;
x_14 = l_Lean_Format_pretty(x_12, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Command_elabSetOption___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = 2;
x_20 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_7, x_19, x_18, x_2, x_3);
lean_dec(x_7);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabSetOption(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_set__option___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isIdent(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getIdAt(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Syntax_getId(x_1);
x_9 = l_Lean_mkOptionalNode___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Command_expandDeclId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_expandDeclId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = l_Lean_Elab_Command_modifyScope___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Syntax_getId(x_10);
x_14 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_13, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
x_3 = x_12;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_4);
x_17 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(x_10, x_13, x_5, x_6);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_withDeclId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid declaration name");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_withDeclId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_withDeclId___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_withDeclId___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_withDeclId___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withDeclId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Elab_Command_expandDeclId(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_Lean_Elab_Command_getLevelNames(x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_174; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_174 = l_Lean_Syntax_isNone(x_7);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_175 = lean_unsigned_to_nat(1u);
x_176 = l_Lean_Syntax_getArg(x_7, x_175);
x_177 = l_Lean_Syntax_getArgs(x_176);
lean_dec(x_176);
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Array_empty___closed__1;
x_181 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_178, x_177, x_179, x_180);
lean_dec(x_177);
lean_inc(x_3);
lean_inc(x_9);
x_182 = l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(x_7, x_181, x_179, x_9, x_3, x_10);
lean_dec(x_181);
lean_dec(x_7);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_11 = x_183;
x_12 = x_184;
goto block_173;
}
else
{
uint8_t x_185; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
return x_182;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_182, 0);
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_182);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_dec(x_7);
lean_inc(x_9);
x_11 = x_9;
x_12 = x_10;
goto block_173;
}
block_173:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_extractMacroScopes(x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 1)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_name_mk_string(x_19, x_18);
lean_ctor_set(x_13, 0, x_20);
x_21 = l_Lean_MacroScopesView_review(x_13);
x_22 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_23 = 1;
lean_inc(x_3);
lean_inc(x_17);
x_24 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_22, x_23, x_17, x_3, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_3);
x_26 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(x_11, x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_3);
x_28 = lean_apply_3(x_2, x_21, x_3, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_3);
lean_inc(x_9);
x_31 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__2(x_9, x_3, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_3);
x_33 = l___private_Lean_Elab_Command_2__getState(x_3, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 2);
x_38 = l_Lean_Name_getNumParts___main(x_17);
lean_dec(x_17);
x_39 = l_List_drop___main___rarg(x_38, x_37);
lean_dec(x_37);
lean_ctor_set(x_34, 2, x_39);
x_40 = l___private_Lean_Elab_Command_3__setState(x_34, x_3, x_35);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_29);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_29);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
x_51 = lean_ctor_get(x_34, 2);
x_52 = lean_ctor_get(x_34, 3);
x_53 = lean_ctor_get(x_34, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
x_54 = l_Lean_Name_getNumParts___main(x_17);
lean_dec(x_17);
x_55 = l_List_drop___main___rarg(x_54, x_51);
lean_dec(x_51);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_56, 4, x_53);
x_57 = l___private_Lean_Elab_Command_3__setState(x_56, x_3, x_35);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_29);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_29);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_33);
if (x_65 == 0)
{
return x_33;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_33);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_29);
lean_dec(x_17);
x_69 = lean_ctor_get(x_31, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_31, 1);
lean_inc(x_70);
lean_dec(x_31);
x_71 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(x_9, x_3, x_70);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_69);
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_17);
x_80 = lean_ctor_get(x_28, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_28, 1);
lean_inc(x_81);
lean_dec(x_28);
x_82 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(x_9, x_3, x_81);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
lean_ctor_set_tag(x_82, 1);
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_80);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
return x_82;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_82);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_26);
if (x_91 == 0)
{
return x_26;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_26, 0);
x_93 = lean_ctor_get(x_26, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_26);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_24);
if (x_95 == 0)
{
return x_24;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_24, 0);
x_97 = lean_ctor_get(x_24, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_24);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_99 = lean_ctor_get(x_13, 1);
x_100 = lean_ctor_get(x_13, 2);
x_101 = lean_ctor_get(x_13, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_13);
x_102 = lean_ctor_get(x_14, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_14, 1);
lean_inc(x_103);
lean_dec(x_14);
x_104 = lean_box(0);
x_105 = lean_name_mk_string(x_104, x_103);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_99);
lean_ctor_set(x_106, 2, x_100);
lean_ctor_set(x_106, 3, x_101);
x_107 = l_Lean_MacroScopesView_review(x_106);
x_108 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_109 = 1;
lean_inc(x_3);
lean_inc(x_102);
x_110 = l___private_Lean_Elab_Command_12__addScopes___main(x_1, x_108, x_109, x_102, x_3, x_12);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
lean_inc(x_3);
x_112 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(x_11, x_3, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
lean_inc(x_3);
x_114 = lean_apply_3(x_2, x_107, x_3, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_3);
lean_inc(x_9);
x_117 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__2(x_9, x_3, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_9);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
lean_inc(x_3);
x_119 = l___private_Lean_Elab_Command_2__getState(x_3, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 4);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
x_128 = l_Lean_Name_getNumParts___main(x_102);
lean_dec(x_102);
x_129 = l_List_drop___main___rarg(x_128, x_124);
lean_dec(x_124);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(0, 5, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_122);
lean_ctor_set(x_130, 1, x_123);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_125);
lean_ctor_set(x_130, 4, x_126);
x_131 = l___private_Lean_Elab_Command_3__setState(x_130, x_3, x_121);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_115);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_115);
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_115);
lean_dec(x_102);
lean_dec(x_3);
x_139 = lean_ctor_get(x_119, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_119, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_141 = x_119;
} else {
 lean_dec_ref(x_119);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_115);
lean_dec(x_102);
x_143 = lean_ctor_get(x_117, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_117, 1);
lean_inc(x_144);
lean_dec(x_117);
x_145 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(x_9, x_3, x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
 lean_ctor_set_tag(x_148, 1);
}
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_143);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_151 = x_145;
} else {
 lean_dec_ref(x_145);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_102);
x_153 = lean_ctor_get(x_114, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_114, 1);
lean_inc(x_154);
lean_dec(x_114);
x_155 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(x_9, x_3, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_153);
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_161 = x_155;
} else {
 lean_dec_ref(x_155);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_163 = lean_ctor_get(x_112, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_112, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_165 = x_112;
} else {
 lean_dec_ref(x_112);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_167 = lean_ctor_get(x_110, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_110, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_169 = x_110;
} else {
 lean_dec_ref(x_110);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_171 = l_Lean_Elab_Command_withDeclId___closed__3;
x_172 = l_Lean_Elab_Command_throwError___rarg(x_1, x_171, x_3, x_12);
return x_172;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_8);
if (x_189 == 0)
{
return x_8;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_8, 0);
x_191 = lean_ctor_get(x_8, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_8);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_withDeclId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_withDeclId(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_5);
if (x_7 == 0)
{
lean_free_object(x_3);
lean_dec(x_5);
x_3 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_2);
x_2 = x_3;
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_10);
if (x_12 == 0)
{
lean_dec(x_10);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_2);
x_2 = x_14;
x_3 = x_11;
goto _start;
}
}
}
}
}
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Array_shrink___main___rarg(x_2, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_fswap(x_2, x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_2 = x_15;
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_swap(x_3, x_4, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Name_inhabited;
x_10 = lean_array_get(x_9, x_3, x_5);
x_11 = l_Lean_Name_lt___main(x_10, x_2);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_swap(x_3, x_4, x_5);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_18 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_3 = x_15;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_37 = l_Lean_Name_inhabited;
x_38 = lean_array_get(x_37, x_1, x_16);
x_39 = lean_array_get(x_37, x_1, x_2);
x_40 = l_Lean_Name_lt___main(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
x_17 = x_1;
goto block_36;
}
else
{
lean_object* x_41; 
x_41 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_41;
goto block_36;
}
block_36:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Name_inhabited;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = l_Lean_Name_lt___main(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get(x_18, x_17, x_16);
x_23 = l_Lean_Name_lt___main(x_22, x_19);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_24 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_3, x_19, x_17, x_2, x_2);
lean_dec(x_19);
x_4 = x_24;
goto block_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
x_25 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_26 = lean_array_get(x_18, x_25, x_3);
lean_inc_n(x_2, 2);
x_27 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_3, x_26, x_25, x_2, x_2);
lean_dec(x_26);
x_4 = x_27;
goto block_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_19);
x_28 = lean_array_swap(x_17, x_2, x_3);
x_29 = lean_array_get(x_18, x_28, x_16);
x_30 = lean_array_get(x_18, x_28, x_3);
x_31 = l_Lean_Name_lt___main(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_32 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_3, x_30, x_28, x_2, x_2);
lean_dec(x_30);
x_4 = x_32;
goto block_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
x_33 = lean_array_swap(x_28, x_16, x_3);
lean_dec(x_16);
x_34 = lean_array_get(x_18, x_33, x_3);
lean_inc_n(x_2, 2);
x_35 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_3, x_34, x_33, x_2, x_2);
lean_dec(x_34);
x_4 = x_35;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
lean_inc(x_1);
x_4 = l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1(x_2, x_3, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(x_1, x_2, x_5, x_5);
lean_dec(x_1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(x_6, x_5, x_9);
lean_dec(x_9);
x_11 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
x_12 = l_List_append___rarg(x_4, x_11);
return x_12;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Elab_Alias(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
lean_object* initialize_Lean_Elab_ResolveName(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Command(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Alias(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_Scope_inhabited___closed__1 = _init_l_Lean_Elab_Command_Scope_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Scope_inhabited___closed__1);
l_Lean_Elab_Command_Scope_inhabited = _init_l_Lean_Elab_Command_Scope_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_Scope_inhabited);
l_Lean_Elab_Command_State_inhabited___closed__1 = _init_l_Lean_Elab_Command_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__1);
l_Lean_Elab_Command_State_inhabited___closed__2 = _init_l_Lean_Elab_Command_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__2);
l_Lean_Elab_Command_State_inhabited___closed__3 = _init_l_Lean_Elab_Command_State_inhabited___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__3);
l_Lean_Elab_Command_State_inhabited___closed__4 = _init_l_Lean_Elab_Command_State_inhabited___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__4);
l_Lean_Elab_Command_State_inhabited = _init_l_Lean_Elab_Command_State_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited);
l_Lean_Elab_Command_Exception_inhabited = _init_l_Lean_Elab_Command_Exception_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_Exception_inhabited);
l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1 = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1);
l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2 = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2);
l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3 = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3);
l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4 = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4);
l_Lean_Elab_Command_CommandElabCoreM_monadState = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__1);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__2 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__2);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__3 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__3);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__4 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__4);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__5 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__5);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__6 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__6);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__7 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__7);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__8 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__8);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__9 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__9);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__10 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__10);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__11 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__11);
l_Lean_Elab_Command_CommandElabM_monadLog = _init_l_Lean_Elab_Command_CommandElabM_monadLog();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4);
l_Lean_Elab_Command_CommandElabM_MonadQuotation = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__1 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__1);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__2 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__2);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__3 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__3);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__4 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__4);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__5 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__5);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__6 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__6);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__7 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__7);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__8 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__8);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__9 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__9);
l_PersistentHashMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__3 = _init_l_PersistentHashMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__3();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Command_commandElabAttribute___spec__1);
l_Lean_Elab_Command_commandElabAttribute___closed__1 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__1);
l_Lean_Elab_Command_commandElabAttribute___closed__2 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__2);
l_Lean_Elab_Command_commandElabAttribute___closed__3 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__3);
l_Lean_Elab_Command_commandElabAttribute___closed__4 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__4);
l_Lean_Elab_Command_commandElabAttribute___closed__5 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__5);
res = l_Lean_Elab_Command_mkCommandElabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_commandElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter);
l_Lean_Elab_Command_elabCommand___main___closed__1 = _init_l_Lean_Elab_Command_elabCommand___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___main___closed__1);
l___private_Lean_Elab_Command_10__toCommandResult___rarg___closed__1 = _init_l___private_Lean_Elab_Command_10__toCommandResult___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_10__toCommandResult___rarg___closed__1);
l_Lean_Elab_Command_CommandElabM_inhabited___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_inhabited___closed__1);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__1 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__1);
l___private_Lean_Elab_Command_12__addScopes___main___closed__1 = _init_l___private_Lean_Elab_Command_12__addScopes___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_12__addScopes___main___closed__1);
l___private_Lean_Elab_Command_12__addScopes___main___closed__2 = _init_l___private_Lean_Elab_Command_12__addScopes___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Command_12__addScopes___main___closed__2);
l___private_Lean_Elab_Command_12__addScopes___main___closed__3 = _init_l___private_Lean_Elab_Command_12__addScopes___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Command_12__addScopes___main___closed__3);
l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabSection___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabSection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabEnd___closed__1 = _init_l_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__1);
l_Lean_Elab_Command_elabEnd___closed__2 = _init_l_Lean_Elab_Command_elabEnd___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__2);
l_Lean_Elab_Command_elabEnd___closed__3 = _init_l_Lean_Elab_Command_elabEnd___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__3);
l_Lean_Elab_Command_elabEnd___closed__4 = _init_l_Lean_Elab_Command_elabEnd___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__4);
l_Lean_Elab_Command_elabEnd___closed__5 = _init_l_Lean_Elab_Command_elabEnd___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__5);
l_Lean_Elab_Command_elabEnd___closed__6 = _init_l_Lean_Elab_Command_elabEnd___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__6);
l_Lean_Elab_Command_elabEnd___closed__7 = _init_l_Lean_Elab_Command_elabEnd___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__7);
l_Lean_Elab_Command_elabEnd___closed__8 = _init_l_Lean_Elab_Command_elabEnd___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__8);
l_Lean_Elab_Command_elabEnd___closed__9 = _init_l_Lean_Elab_Command_elabEnd___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__9);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabEnd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_modifyScope___closed__1 = _init_l_Lean_Elab_Command_modifyScope___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__1);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5);
l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elbChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_logUnknownDecl___closed__1 = _init_l_Lean_Elab_Command_logUnknownDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_logUnknownDecl___closed__1);
l_Lean_Elab_Command_logUnknownDecl___closed__2 = _init_l_Lean_Elab_Command_logUnknownDecl___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_logUnknownDecl___closed__2);
l_Lean_Elab_Command_elabExport___closed__1 = _init_l_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__1);
l_Lean_Elab_Command_elabExport___closed__2 = _init_l_Lean_Elab_Command_elabExport___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__2);
l_Lean_Elab_Command_elabExport___closed__3 = _init_l_Lean_Elab_Command_elabExport___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__3);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabExport(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabOpen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabVariable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabVariables(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabCheck___closed__1 = _init_l_Lean_Elab_Command_elabCheck___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__1);
l_Lean_Elab_Command_elabCheck___closed__2 = _init_l_Lean_Elab_Command_elabCheck___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__2);
l_Lean_Elab_Command_elabCheck___closed__3 = _init_l_Lean_Elab_Command_elabCheck___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__3);
l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1);
l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2);
res = l___regBuiltin_Lean_Elab_Command_elabCheck(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_failIfSucceeds___closed__1 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__1);
l_Lean_Elab_Command_failIfSucceeds___closed__2 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__2);
l_Lean_Elab_Command_failIfSucceeds___closed__3 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__3);
l_Lean_Elab_Command_failIfSucceeds___closed__4 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__4);
l_Lean_Elab_Command_failIfSucceeds___closed__5 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__5);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__4 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__4);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__5 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__5);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__6 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__6);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__7 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__7);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__8 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__8);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__9 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__9);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__10 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__10);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__11 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__11);
l_Lean_Elab_Command_elabEvalUnsafe___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__3);
l___regBuiltin_Lean_Elab_Command_elabEval___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabEval(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSynth___closed__1 = _init_l_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__1);
l_Lean_Elab_Command_elabSynth___closed__2 = _init_l_Lean_Elab_Command_elabSynth___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__2);
l_Lean_Elab_Command_elabSynth___closed__3 = _init_l_Lean_Elab_Command_elabSynth___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabSynth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_setOption___closed__1 = _init_l_Lean_Elab_Command_setOption___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__1);
l_Lean_Elab_Command_setOption___closed__2 = _init_l_Lean_Elab_Command_setOption___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__2);
l_Lean_Elab_Command_setOption___closed__3 = _init_l_Lean_Elab_Command_setOption___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__3);
l_Lean_Elab_Command_elabSetOption___closed__1 = _init_l_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__1);
l_Lean_Elab_Command_elabSetOption___closed__2 = _init_l_Lean_Elab_Command_elabSetOption___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__2);
l_Lean_Elab_Command_elabSetOption___closed__3 = _init_l_Lean_Elab_Command_elabSetOption___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_withDeclId___closed__1 = _init_l_Lean_Elab_Command_withDeclId___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_withDeclId___closed__1);
l_Lean_Elab_Command_withDeclId___closed__2 = _init_l_Lean_Elab_Command_withDeclId___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_withDeclId___closed__2);
l_Lean_Elab_Command_withDeclId___closed__3 = _init_l_Lean_Elab_Command_withDeclId___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_withDeclId___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

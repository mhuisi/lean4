// Lean compiler output
// Module: Lean.Meta.SynthInstance
// Imports: Lean.Meta.Basic Lean.Meta.Instances Lean.Meta.LevelDefEq Lean.Meta.AbstractMVars Lean.Meta.WHNF
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__51;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__3;
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__1(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toLOption___rarg(lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1;
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__1;
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__7;
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__3;
lean_object* l___private_Lean_Meta_SynthInstance_7__regTraceClasses(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_addAnswer___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocessLevels___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__5;
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
lean_object* l_Lean_Meta_synthPendingImp(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__3;
lean_object* l_Lean_Meta_SynthInstance_getTraceState___boxed(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__1;
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__2(lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Answer_inhabited;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_withMCtx(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5;
extern lean_object* l_Lean_Meta_Exception_Inhabited___closed__1;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKey___closed__2;
lean_object* l_Lean_Meta_SynthInstance_main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_maxStepsOption___closed__3;
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__5;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__73;
extern lean_object* l_Lean_Meta_AbstractMVarsResult_inhabited___closed__1;
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setSynthPendingRef___closed__1;
uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object*);
extern lean_object* l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_meta2Synth(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__6;
lean_object* l_Lean_Meta_SynthInstance_getTraceState(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getOptions(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__3;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__5;
lean_object* l_Lean_Meta_SynthInstance_meta2Synth___closed__1;
lean_object* l_Lean_Meta_SynthInstance_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__7;
lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__6___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_GeneratorNode_inhabited;
lean_object* l_Lean_Meta_SynthInstance_getTraceState___rarg(lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_getGlobalInstances___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__4;
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1;
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_step(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setSynthPendingRef(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__9;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_main___spec__1(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__5;
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__3;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__7;
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__4;
size_t l_USize_land(size_t, size_t);
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__4;
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___closed__6;
lean_object* l_Lean_Meta_SynthInstance_synth(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__2;
uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getEntry___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getUnify___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__2;
lean_object* l_Lean_Meta_synthInstance_x3f___closed__3;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocessLevels(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__5;
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2;
lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_withMCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_object* l_Lean_Meta_SynthInstance_getTop___rarg(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__6;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__6;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__8;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
lean_object* l_Lean_Meta_SynthInstance_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object*);
extern lean_object* l_Lean_Meta_synthPendingRef;
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_synth___main___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tracer;
lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_6__getMaxSteps(lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__72;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__4;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isLevelAssignable(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__9;
lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
lean_object* l_Lean_Meta_SynthInstance_Consumernode_inhabited;
extern lean_object* l_Lean_Meta_isLevelDefEq___closed__9;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_6__getMaxSteps___boxed(lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_generate___closed__2;
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_SynthInstance_generate___closed__1;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__1;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1;
lean_object* l_Lean_Meta_maxStepsOption___closed__2;
lean_object* l_Lean_Meta_SynthInstance_getInstances___closed__1;
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___boxed(lean_object*);
uint8_t l_Lean_MetavarContext_isExprAssignable(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_SynthInstance_liftMeta___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__3;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
extern lean_object* l___private_Lean_Meta_Basic_10__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_SynthInstance_consume(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__4;
lean_object* l_Lean_Meta_synthInstance_x3f___closed__2;
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2;
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__1;
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_tracer___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__2;
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_has_out_params(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_resume___closed__2;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___closed__8;
lean_object* l_Lean_Meta_SynthInstance_generate___closed__4;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_main___closed__1;
lean_object* l_Lean_Meta_SynthInstance_resume___closed__1;
lean_object* l_Lean_Meta_SynthInstance_wakeUp___closed__3;
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_Meta_maxStepsOption___closed__4;
lean_object* l_Lean_Meta_SynthInstance_liftMeta(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_forMAux___main___at___private_Lean_MetavarContext_10__collectDeps___spec__50___closed__1;
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inferTCGoalsLR");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instruct type class resolution procedure to solve goals from left to right for this instance");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2;
x_3 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3;
x_4 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SynthInstance_hasInferTCGoalsLRAttribute(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Expr_Inhabited___closed__1;
x_2 = l_Lean_MetavarContext_Inhabited___closed__1;
x_3 = l_Array_empty___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_Inhabited___closed__1;
x_3 = l_Lean_MetavarContext_Inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1;
return x_1;
}
}
uint8_t l_Lean_Meta_SynthInstance_Waiter_isRoot(lean_object* x_1) {
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
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_Waiter_isRoot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SynthInstance_Waiter_isRoot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__7(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__5(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tc");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Level_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_6, x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_level_update_succ(x_1, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_level_update_succ(x_1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_2);
x_17 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_15, x_2, x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_16, x_2, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_level_update_max(x_1, x_18, x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_level_update_max(x_1, x_18, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_2);
x_30 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_28, x_2, x_3);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_29, x_2, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_level_update_imax(x_1, x_31, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_level_update_imax(x_1, x_31, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
case 5:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = l_Lean_MetavarContext_isLevelAssignable(x_2, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
x_47 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(x_45, x_41);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_3, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_3, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_3, 0);
lean_dec(x_51);
x_52 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_inc(x_44);
x_53 = lean_name_mk_numeral(x_52, x_44);
x_54 = l_Lean_mkLevelParam(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_44, x_55);
lean_dec(x_44);
lean_inc(x_54);
x_57 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(x_45, x_41, x_54);
lean_ctor_set(x_3, 1, x_57);
lean_ctor_set(x_3, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
x_59 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_inc(x_44);
x_60 = lean_name_mk_numeral(x_59, x_44);
x_61 = l_Lean_mkLevelParam(x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_44, x_62);
lean_dec(x_44);
lean_inc(x_61);
x_64 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__3(x_45, x_41, x_61);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_46);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_41);
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
}
}
default: 
{
lean_object* x_69; 
lean_dec(x_2);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_3);
return x_69;
}
}
}
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__7(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__5(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_9 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_7, x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(x_8, x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_2);
x_20 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_18, x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(x_19, x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_MetavarContext_isExprAssignable(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_inc(x_9);
x_18 = lean_name_mk_numeral(x_17, x_9);
x_19 = l_Lean_mkFVar(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_9, x_20);
lean_dec(x_9);
lean_inc(x_19);
x_22 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(x_11, x_6, x_19);
lean_ctor_set(x_3, 2, x_22);
lean_ctor_set(x_3, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_24 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2;
lean_inc(x_9);
x_25 = lean_name_mk_numeral(x_24, x_9);
x_26 = l_Lean_mkFVar(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_9, x_27);
lean_dec(x_9);
lean_inc(x_26);
x_29 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__3(x_11, x_6, x_26);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
}
case 3:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main(x_34, x_2, x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_expr_update_sort(x_1, x_37);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_expr_update_sort(x_1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
case 4:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = l_List_mapM___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__9(x_43, x_2, x_3);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_expr_update_const(x_1, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_expr_update_const(x_1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
case 5:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_2);
x_54 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_52, x_2, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_53, x_2, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_expr_update_app(x_1, x_55, x_59);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_expr_update_app(x_1, x_55, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
case 6:
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_2);
x_68 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_65, x_2, x_3);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_66, x_2, x_70);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = (uint8_t)((x_67 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_1, x_74, x_69, x_73);
lean_ctor_set(x_71, 0, x_75);
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_71, 0);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_71);
x_78 = (uint8_t)((x_67 << 24) >> 61);
x_79 = lean_expr_update_lambda(x_1, x_78, x_69, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
case 7:
{
lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 2);
lean_inc(x_82);
x_83 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_2);
x_84 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_81, x_2, x_3);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_82, x_2, x_86);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = (uint8_t)((x_83 << 24) >> 61);
x_91 = lean_expr_update_forall(x_1, x_90, x_85, x_89);
lean_ctor_set(x_87, 0, x_91);
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
x_94 = (uint8_t)((x_83 << 24) >> 61);
x_95 = lean_expr_update_forall(x_1, x_94, x_85, x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
case 8:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_1, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 3);
lean_inc(x_99);
lean_inc(x_2);
x_100 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_97, x_2, x_3);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_2);
x_103 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_98, x_2, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_99, x_2, x_105);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_expr_update_let(x_1, x_101, x_104, x_108);
lean_ctor_set(x_106, 0, x_109);
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_expr_update_let(x_1, x_101, x_104, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
case 10:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
x_115 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_114, x_2, x_3);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_expr_update_mdata(x_1, x_117);
lean_ctor_set(x_115, 0, x_118);
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_115);
x_121 = lean_expr_update_mdata(x_1, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
case 11:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_1, 2);
lean_inc(x_123);
x_124 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_123, x_2, x_3);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_expr_update_proj(x_1, x_126);
lean_ctor_set(x_124, 0, x_127);
return x_124;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_124, 0);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_124);
x_130 = lean_expr_update_proj(x_1, x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
default: 
{
lean_object* x_132; 
lean_dec(x_2);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_3);
return x_132;
}
}
}
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_MkTableKey_normExpr___main___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_MkTableKey_normExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_mkTableKey___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_SynthInstance_mkTableKey___closed__1;
x_3 = l_Lean_Meta_SynthInstance_mkTableKey___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkTableKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_SynthInstance_mkTableKey___closed__3;
x_4 = l_Lean_Meta_SynthInstance_MkTableKey_normExpr___main(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_AbstractMVarsResult_inhabited___closed__1;
x_2 = l_Lean_Expr_Inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_Answer_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_Inhabited___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1;
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getTraceState___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTraceState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getTraceState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SynthInstance_getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
lean_object* l_Lean_Meta_SynthInstance_addContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_addContext(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_5, 4, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set(x_3, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 5);
lean_inc(x_31);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_32 = x_21;
} else {
 lean_dec_ref(x_21);
 x_32 = lean_box(0);
}
x_33 = lean_apply_1(x_1, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_31);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set(x_35, 4, x_25);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getOptions___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getTraceState___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_addContext___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_SynthInstance_tracer___closed__1;
x_2 = l_Lean_Meta_SynthInstance_tracer___closed__2;
x_3 = l_Lean_Meta_SynthInstance_tracer___closed__3;
x_4 = l_Lean_Meta_SynthInstance_tracer___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tracer() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_tracer___closed__5;
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_liftMeta___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_apply_2(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_3, 0, x_8);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_3, 0, x_13);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_ctor_get(x_3, 3);
x_21 = lean_ctor_get(x_3, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_22 = lean_apply_2(x_1, x_2, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_liftMeta(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_liftMeta___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_meta2Synth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_liftMeta___rarg), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_meta2Synth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_meta2Synth___closed__1;
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_withMCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_6, 1, x_1);
x_9 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_11, 1);
lean_dec(x_17);
lean_ctor_set(x_11, 1, x_8);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 2);
x_20 = lean_ctor_get(x_11, 3);
x_21 = lean_ctor_get(x_11, 4);
x_22 = lean_ctor_get(x_11, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_10, 0, x_23);
return x_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_10, 2);
x_26 = lean_ctor_get(x_10, 3);
x_27 = lean_ctor_get(x_10, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_11, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_33 = x_11;
} else {
 lean_dec_ref(x_11);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_9, 1, x_35);
return x_9;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
lean_dec(x_9);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_10, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_10, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_10, 4);
lean_inc(x_40);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_41 = x_10;
} else {
 lean_dec_ref(x_10);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_11, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 5);
lean_inc(x_46);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_47 = x_11;
} else {
 lean_dec_ref(x_11);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 6, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_8);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_44);
lean_ctor_set(x_48, 4, x_45);
lean_ctor_set(x_48, 5, x_46);
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 5, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_39);
lean_ctor_set(x_49, 4, x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_9, 1);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_51, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_52, 1);
lean_dec(x_58);
lean_ctor_set(x_52, 1, x_8);
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_52, 2);
x_61 = lean_ctor_get(x_52, 3);
x_62 = lean_ctor_get(x_52, 4);
x_63 = lean_ctor_get(x_52, 5);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_52);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_8);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_63);
lean_ctor_set(x_51, 0, x_64);
return x_9;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_51, 1);
x_66 = lean_ctor_get(x_51, 2);
x_67 = lean_ctor_get(x_51, 3);
x_68 = lean_ctor_get(x_51, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_52, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_52, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_52, 5);
lean_inc(x_73);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_74 = x_52;
} else {
 lean_dec_ref(x_52);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 6, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_8);
lean_ctor_set(x_75, 2, x_70);
lean_ctor_set(x_75, 3, x_71);
lean_ctor_set(x_75, 4, x_72);
lean_ctor_set(x_75, 5, x_73);
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_65);
lean_ctor_set(x_76, 2, x_66);
lean_ctor_set(x_76, 3, x_67);
lean_ctor_set(x_76, 4, x_68);
lean_ctor_set(x_9, 1, x_76);
return x_9;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_77 = lean_ctor_get(x_9, 0);
lean_inc(x_77);
lean_dec(x_9);
x_78 = lean_ctor_get(x_51, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_51, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_51, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_51, 4);
lean_inc(x_81);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 x_82 = x_51;
} else {
 lean_dec_ref(x_51);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_52, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_52, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_52, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_52, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_52, 5);
lean_inc(x_87);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_88 = x_52;
} else {
 lean_dec_ref(x_52);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 6, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_8);
lean_ctor_set(x_89, 2, x_84);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_86);
lean_ctor_set(x_89, 5, x_87);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
lean_ctor_set(x_90, 2, x_79);
lean_ctor_set(x_90, 3, x_80);
lean_ctor_set(x_90, 4, x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_6, 0);
x_93 = lean_ctor_get(x_6, 1);
x_94 = lean_ctor_get(x_6, 2);
x_95 = lean_ctor_get(x_6, 3);
x_96 = lean_ctor_get(x_6, 4);
x_97 = lean_ctor_get(x_6, 5);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_6);
x_98 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_1);
lean_ctor_set(x_98, 2, x_94);
lean_ctor_set(x_98, 3, x_95);
lean_ctor_set(x_98, 4, x_96);
lean_ctor_set(x_98, 5, x_97);
lean_ctor_set(x_4, 0, x_98);
x_99 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 4);
lean_inc(x_107);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 x_108 = x_100;
} else {
 lean_dec_ref(x_100);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_101, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_101, 4);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 5);
lean_inc(x_113);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 x_114 = x_101;
} else {
 lean_dec_ref(x_101);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 6, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_93);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_111);
lean_ctor_set(x_115, 4, x_112);
lean_ctor_set(x_115, 5, x_113);
if (lean_is_scalar(x_108)) {
 x_116 = lean_alloc_ctor(0, 5, 0);
} else {
 x_116 = x_108;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_104);
lean_ctor_set(x_116, 2, x_105);
lean_ctor_set(x_116, 3, x_106);
lean_ctor_set(x_116, 4, x_107);
if (lean_is_scalar(x_103)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_103;
}
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_118 = lean_ctor_get(x_99, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_99, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_121 = x_99;
} else {
 lean_dec_ref(x_99);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 4);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_119, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_119, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 5);
lean_inc(x_131);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 x_132 = x_119;
} else {
 lean_dec_ref(x_119);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_93);
lean_ctor_set(x_133, 2, x_128);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_130);
lean_ctor_set(x_133, 5, x_131);
if (lean_is_scalar(x_126)) {
 x_134 = lean_alloc_ctor(0, 5, 0);
} else {
 x_134 = x_126;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_122);
lean_ctor_set(x_134, 2, x_123);
lean_ctor_set(x_134, 3, x_124);
lean_ctor_set(x_134, 4, x_125);
if (lean_is_scalar(x_121)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_121;
}
lean_ctor_set(x_135, 0, x_120);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_136 = lean_ctor_get(x_4, 0);
x_137 = lean_ctor_get(x_4, 1);
x_138 = lean_ctor_get(x_4, 2);
x_139 = lean_ctor_get(x_4, 3);
x_140 = lean_ctor_get(x_4, 4);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_4);
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_136, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_136, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_136, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_136, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 lean_ctor_release(x_136, 4);
 lean_ctor_release(x_136, 5);
 x_147 = x_136;
} else {
 lean_dec_ref(x_136);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 6, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_1);
lean_ctor_set(x_148, 2, x_143);
lean_ctor_set(x_148, 3, x_144);
lean_ctor_set(x_148, 4, x_145);
lean_ctor_set(x_148, 5, x_146);
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_137);
lean_ctor_set(x_149, 2, x_138);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set(x_149, 4, x_140);
x_150 = lean_apply_2(x_2, x_3, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 4);
lean_inc(x_158);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 x_159 = x_151;
} else {
 lean_dec_ref(x_151);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_152, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_152, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_152, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_152, 4);
lean_inc(x_163);
x_164 = lean_ctor_get(x_152, 5);
lean_inc(x_164);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 lean_ctor_release(x_152, 5);
 x_165 = x_152;
} else {
 lean_dec_ref(x_152);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 6, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_160);
lean_ctor_set(x_166, 1, x_142);
lean_ctor_set(x_166, 2, x_161);
lean_ctor_set(x_166, 3, x_162);
lean_ctor_set(x_166, 4, x_163);
lean_ctor_set(x_166, 5, x_164);
if (lean_is_scalar(x_159)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_159;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_155);
lean_ctor_set(x_167, 2, x_156);
lean_ctor_set(x_167, 3, x_157);
lean_ctor_set(x_167, 4, x_158);
if (lean_is_scalar(x_154)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_154;
}
lean_ctor_set(x_168, 0, x_153);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_169 = lean_ctor_get(x_150, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_150, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_172 = x_150;
} else {
 lean_dec_ref(x_150);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 4);
lean_inc(x_176);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 x_177 = x_169;
} else {
 lean_dec_ref(x_169);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_170, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_170, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 3);
lean_inc(x_180);
x_181 = lean_ctor_get(x_170, 4);
lean_inc(x_181);
x_182 = lean_ctor_get(x_170, 5);
lean_inc(x_182);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 lean_ctor_release(x_170, 5);
 x_183 = x_170;
} else {
 lean_dec_ref(x_170);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 6, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_142);
lean_ctor_set(x_184, 2, x_179);
lean_ctor_set(x_184, 3, x_180);
lean_ctor_set(x_184, 4, x_181);
lean_ctor_set(x_184, 5, x_182);
if (lean_is_scalar(x_177)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_177;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_173);
lean_ctor_set(x_185, 2, x_174);
lean_ctor_set(x_185, 3, x_175);
lean_ctor_set(x_185, 4, x_176);
if (lean_is_scalar(x_172)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_172;
}
lean_ctor_set(x_186, 0, x_171);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_withMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_withMCtx___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_7, x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_18, x_2, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.SynthInstance");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("global instance is not a constant");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(192u);
x_3 = lean_unsigned_to_nat(13u);
x_4 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_25; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_25 = x_9;
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_26, x_3, x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_expr_update_const(x_25, x_29);
lean_ctor_set(x_27, 0, x_30);
x_12 = x_27;
goto block_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_expr_update_const(x_25, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_12 = x_34;
goto block_24;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
x_35 = l_Lean_Meta_isClassQuick___main___closed__1;
x_36 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3;
x_37 = lean_panic_fn(x_35, x_36);
lean_inc(x_3);
x_38 = lean_apply_2(x_37, x_3, x_4);
x_12 = x_38;
goto block_24;
}
block_24:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_1, x_15);
x_17 = x_13;
x_18 = lean_array_fset(x_11, x_1, x_17);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_18;
x_4 = x_14;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_8);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_8);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_10__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__72;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("globalInstances");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Meta_isClass(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_alloc_ctor(15, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_alloc_ctor(15, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lean_Meta_getGlobalInstances___rarg(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Lean_Meta_DiscrTree_getUnify___rarg(x_29, x_2, x_3, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = x_32;
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2), 4, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_34);
x_37 = x_36;
lean_inc(x_3);
x_38 = lean_apply_2(x_37, x_3, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_64; uint8_t x_65; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_64 = lean_ctor_get(x_40, 4);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = 0;
x_42 = x_66;
x_43 = x_40;
goto block_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_68 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_67, x_3, x_40);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_42 = x_71;
x_43 = x_70;
goto block_63;
}
block_63:
{
if (x_42 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
x_45 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_3, x_27, x_44, x_35, x_39);
lean_dec(x_44);
lean_dec(x_27);
lean_dec(x_3);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_41);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_2);
x_48 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_51 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_39, x_35, x_50);
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_54 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_53, x_52, x_3, x_43);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_3, x_27, x_57, x_35, x_39);
lean_dec(x_57);
lean_dec(x_27);
lean_dec(x_3);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
x_61 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_3, x_27, x_60, x_35, x_39);
lean_dec(x_60);
lean_dec(x_27);
lean_dec(x_3);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_38);
if (x_72 == 0)
{
return x_38;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_38, 0);
x_74 = lean_ctor_get(x_38, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_38);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_31);
if (x_76 == 0)
{
return x_31;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_31, 0);
x_78 = lean_ctor_get(x_31, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_31);
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
uint8_t x_80; 
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_5);
if (x_80 == 0)
{
return x_5;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_5, 0);
x_82 = lean_ctor_get(x_5, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_5);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getInstances___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_5 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM___main___at_Lean_Meta_SynthInstance_getInstances___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_getInstances___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_Meta_SynthInstance_newSubgoal___spec__3(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__6(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_SynthInstance_getOptions(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_checkTraceOption(x_6, x_1);
lean_dec(x_6);
x_8 = lean_box(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_Lean_checkTraceOption(x_9, x_1);
lean_dec(x_9);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_Meta_SynthInstance_addContext(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 4);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_10);
x_19 = l_PersistentArray_push___rarg(x_17, x_18);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_box(0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_10);
x_24 = l_PersistentArray_push___rarg(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_21);
lean_ctor_set(x_7, 4, x_25);
x_26 = lean_box(0);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = lean_ctor_get(x_7, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_32 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_34 = x_8;
} else {
 lean_dec_ref(x_8);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_10);
x_36 = l_PersistentArray_push___rarg(x_33, x_35);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 1, 1);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set(x_38, 3, x_30);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_31);
lean_ctor_set(x_6, 0, x_38);
x_39 = lean_box(0);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_6, 1);
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_ctor_get(x_6, 3);
x_43 = lean_ctor_get(x_6, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_6);
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_49 = x_7;
} else {
 lean_dec_ref(x_7);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_52 = x_8;
} else {
 lean_dec_ref(x_8);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_10);
x_54 = l_PersistentArray_push___rarg(x_51, x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 1, 1);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_50);
if (lean_is_scalar(x_49)) {
 x_56 = lean_alloc_ctor(0, 6, 0);
} else {
 x_56 = x_49;
}
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_48);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_40);
lean_ctor_set(x_57, 2, x_41);
lean_ctor_set(x_57, 3, x_42);
lean_ctor_set(x_57, 4, x_43);
x_58 = lean_box(0);
lean_ctor_set(x_5, 1, x_57);
lean_ctor_set(x_5, 0, x_58);
return x_5;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_59 = lean_ctor_get(x_5, 0);
lean_inc(x_59);
lean_dec(x_5);
x_60 = lean_ctor_get(x_6, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_6, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_6, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 4);
lean_inc(x_63);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_64 = x_6;
} else {
 lean_dec_ref(x_6);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_7, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_7, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_7, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_70 = x_7;
} else {
 lean_dec_ref(x_7);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_72 = lean_ctor_get(x_8, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_73 = x_8;
} else {
 lean_dec_ref(x_8);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_59);
x_75 = l_PersistentArray_push___rarg(x_72, x_74);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_71);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_66);
lean_ctor_set(x_77, 2, x_67);
lean_ctor_set(x_77, 3, x_68);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_69);
if (lean_is_scalar(x_64)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_64;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_60);
lean_ctor_set(x_78, 2, x_61);
lean_ctor_set(x_78, 3, x_62);
lean_ctor_set(x_78, 4, x_63);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("newSubgoal");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_newSubgoal___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_newSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_12 = x_6;
} else {
 lean_dec_ref(x_6);
 x_12 = lean_box(0);
}
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_44; lean_object* x_45; lean_object* x_73; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_14 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_7, 1, x_1);
x_143 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_143, 0, x_7);
lean_ctor_set(x_143, 1, x_8);
lean_ctor_set(x_143, 2, x_9);
lean_ctor_set(x_143, 3, x_10);
lean_ctor_set(x_143, 4, x_11);
x_144 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_145, sizeof(void*)*1);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_73 = x_147;
goto block_142;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_150 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_149, x_5, x_148);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_73 = x_153;
goto block_142;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec(x_150);
lean_inc(x_2);
x_155 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_155, 0, x_2);
x_156 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_149, x_155, x_5, x_154);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_73 = x_157;
goto block_142;
}
}
block_43:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_dec(x_20);
lean_ctor_set(x_18, 1, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 2);
x_24 = lean_ctor_get(x_18, 3);
x_25 = lean_ctor_get(x_18, 4);
x_26 = lean_ctor_get(x_18, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_16, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_16);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
x_31 = lean_ctor_get(x_16, 2);
x_32 = lean_ctor_get(x_16, 3);
x_33 = lean_ctor_get(x_16, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 5);
lean_inc(x_38);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 x_39 = x_29;
} else {
 lean_dec_ref(x_29);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 6, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_14);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_38);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
block_72:
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 1);
lean_dec(x_49);
lean_ctor_set(x_47, 1, x_14);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 2);
x_53 = lean_ctor_get(x_47, 3);
x_54 = lean_ctor_get(x_47, 4);
x_55 = lean_ctor_get(x_47, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_14);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_53);
lean_ctor_set(x_56, 4, x_54);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_45, 0, x_56);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_45);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_ctor_get(x_45, 1);
x_60 = lean_ctor_get(x_45, 2);
x_61 = lean_ctor_get(x_45, 3);
x_62 = lean_ctor_get(x_45, 4);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_45);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 5);
lean_inc(x_67);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 lean_ctor_release(x_58, 5);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_14);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_65);
lean_ctor_set(x_69, 4, x_66);
lean_ctor_set(x_69, 5, x_67);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_60);
lean_ctor_set(x_70, 3, x_61);
lean_ctor_set(x_70, 4, x_62);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_44);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
block_142:
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_ctor_get(x_73, 2);
x_78 = lean_ctor_get(x_73, 3);
x_79 = lean_ctor_get(x_73, 4);
lean_inc(x_5);
lean_inc(x_3);
x_80 = l_Lean_Meta_inferType(x_3, x_5, x_75);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Meta_instantiateMVars(x_81, x_5, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_87 = l_Lean_Meta_forallTelescopeReducing___rarg(x_84, x_86, x_5, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_89);
lean_ctor_set(x_73, 0, x_89);
x_91 = l_Array_isEmpty___rarg(x_88);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_73);
x_92 = lean_array_get_size(x_88);
lean_inc(x_2);
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_3);
lean_ctor_set(x_93, 1, x_2);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_88);
lean_ctor_set(x_93, 4, x_92);
x_94 = l_Lean_mkOptionalNode___closed__2;
x_95 = lean_array_push(x_94, x_4);
x_96 = l_Array_empty___closed__1;
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_push(x_77, x_93);
x_99 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_79, x_2, x_97);
if (lean_is_scalar(x_12)) {
 x_100 = lean_alloc_ctor(0, 5, 0);
} else {
 x_100 = x_12;
}
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_76);
lean_ctor_set(x_100, 2, x_98);
lean_ctor_set(x_100, 3, x_78);
lean_ctor_set(x_100, 4, x_99);
x_101 = lean_box(0);
x_15 = x_101;
x_16 = x_100;
goto block_43;
}
else
{
lean_object* x_102; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = lean_box(0);
x_15 = x_102;
x_16 = x_73;
goto block_43;
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_87, 1);
lean_inc(x_104);
lean_dec(x_87);
lean_ctor_set(x_73, 0, x_104);
x_44 = x_103;
x_45 = x_73;
goto block_72;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_ctor_get(x_80, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_80, 1);
lean_inc(x_106);
lean_dec(x_80);
lean_ctor_set(x_73, 0, x_106);
x_44 = x_105;
x_45 = x_73;
goto block_72;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_73, 0);
x_108 = lean_ctor_get(x_73, 1);
x_109 = lean_ctor_get(x_73, 2);
x_110 = lean_ctor_get(x_73, 3);
x_111 = lean_ctor_get(x_73, 4);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_73);
lean_inc(x_5);
lean_inc(x_3);
x_112 = l_Lean_Meta_inferType(x_3, x_5, x_107);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Meta_instantiateMVars(x_113, x_5, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_119 = l_Lean_Meta_forallTelescopeReducing___rarg(x_116, x_118, x_5, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_121);
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_108);
lean_ctor_set(x_123, 2, x_109);
lean_ctor_set(x_123, 3, x_110);
lean_ctor_set(x_123, 4, x_111);
x_124 = l_Array_isEmpty___rarg(x_120);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_123);
x_125 = lean_array_get_size(x_120);
lean_inc(x_2);
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_3);
lean_ctor_set(x_126, 1, x_2);
lean_ctor_set(x_126, 2, x_122);
lean_ctor_set(x_126, 3, x_120);
lean_ctor_set(x_126, 4, x_125);
x_127 = l_Lean_mkOptionalNode___closed__2;
x_128 = lean_array_push(x_127, x_4);
x_129 = l_Array_empty___closed__1;
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_array_push(x_109, x_126);
x_132 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_111, x_2, x_130);
if (lean_is_scalar(x_12)) {
 x_133 = lean_alloc_ctor(0, 5, 0);
} else {
 x_133 = x_12;
}
lean_ctor_set(x_133, 0, x_121);
lean_ctor_set(x_133, 1, x_108);
lean_ctor_set(x_133, 2, x_131);
lean_ctor_set(x_133, 3, x_110);
lean_ctor_set(x_133, 4, x_132);
x_134 = lean_box(0);
x_15 = x_134;
x_16 = x_133;
goto block_43;
}
else
{
lean_object* x_135; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_box(0);
x_15 = x_135;
x_16 = x_123;
goto block_43;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = lean_ctor_get(x_119, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_119, 1);
lean_inc(x_137);
lean_dec(x_119);
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_108);
lean_ctor_set(x_138, 2, x_109);
lean_ctor_set(x_138, 3, x_110);
lean_ctor_set(x_138, 4, x_111);
x_44 = x_136;
x_45 = x_138;
goto block_72;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_ctor_get(x_112, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_112, 1);
lean_inc(x_140);
lean_dec(x_112);
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_108);
lean_ctor_set(x_141, 2, x_109);
lean_ctor_set(x_141, 3, x_110);
lean_ctor_set(x_141, 4, x_111);
x_44 = x_139;
x_45 = x_141;
goto block_72;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_182; lean_object* x_183; lean_object* x_200; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_158 = lean_ctor_get(x_7, 0);
x_159 = lean_ctor_get(x_7, 1);
x_160 = lean_ctor_get(x_7, 2);
x_161 = lean_ctor_get(x_7, 3);
x_162 = lean_ctor_get(x_7, 4);
x_163 = lean_ctor_get(x_7, 5);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_7);
x_238 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_238, 0, x_158);
lean_ctor_set(x_238, 1, x_1);
lean_ctor_set(x_238, 2, x_160);
lean_ctor_set(x_238, 3, x_161);
lean_ctor_set(x_238, 4, x_162);
lean_ctor_set(x_238, 5, x_163);
x_239 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_8);
lean_ctor_set(x_239, 2, x_9);
lean_ctor_set(x_239, 3, x_10);
lean_ctor_set(x_239, 4, x_11);
x_240 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_239);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get_uint8(x_241, sizeof(void*)*1);
lean_dec(x_241);
if (x_242 == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_200 = x_243;
goto block_237;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
lean_dec(x_240);
x_245 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_246 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_245, x_5, x_244);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_unbox(x_247);
lean_dec(x_247);
if (x_248 == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_200 = x_249;
goto block_237;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
lean_inc(x_2);
x_251 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_251, 0, x_2);
x_252 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_245, x_251, x_5, x_250);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_200 = x_253;
goto block_237;
}
}
block_181:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 4);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 lean_ctor_release(x_165, 4);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_166, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_166, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_166, 4);
lean_inc(x_175);
x_176 = lean_ctor_get(x_166, 5);
lean_inc(x_176);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 lean_ctor_release(x_166, 5);
 x_177 = x_166;
} else {
 lean_dec_ref(x_166);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 6, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_159);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_174);
lean_ctor_set(x_178, 4, x_175);
lean_ctor_set(x_178, 5, x_176);
if (lean_is_scalar(x_171)) {
 x_179 = lean_alloc_ctor(0, 5, 0);
} else {
 x_179 = x_171;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_167);
lean_ctor_set(x_179, 2, x_168);
lean_ctor_set(x_179, 3, x_169);
lean_ctor_set(x_179, 4, x_170);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_164);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
block_199:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 4);
lean_inc(x_188);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 lean_ctor_release(x_183, 3);
 lean_ctor_release(x_183, 4);
 x_189 = x_183;
} else {
 lean_dec_ref(x_183);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_184, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 4);
lean_inc(x_193);
x_194 = lean_ctor_get(x_184, 5);
lean_inc(x_194);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 x_195 = x_184;
} else {
 lean_dec_ref(x_184);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 6, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_190);
lean_ctor_set(x_196, 1, x_159);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 3, x_192);
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 5, x_194);
if (lean_is_scalar(x_189)) {
 x_197 = lean_alloc_ctor(0, 5, 0);
} else {
 x_197 = x_189;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_185);
lean_ctor_set(x_197, 2, x_186);
lean_ctor_set(x_197, 3, x_187);
lean_ctor_set(x_197, 4, x_188);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_182);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
block_237:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 4);
lean_inc(x_205);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 x_206 = x_200;
} else {
 lean_dec_ref(x_200);
 x_206 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_3);
x_207 = l_Lean_Meta_inferType(x_3, x_5, x_201);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l_Lean_Meta_instantiateMVars(x_208, x_5, x_209);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = l_Lean_Meta_SynthInstance_getInstances___closed__1;
x_214 = l_Lean_Meta_forallTelescopeReducing___rarg(x_211, x_213, x_5, x_212);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_216);
if (lean_is_scalar(x_206)) {
 x_218 = lean_alloc_ctor(0, 5, 0);
} else {
 x_218 = x_206;
}
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_202);
lean_ctor_set(x_218, 2, x_203);
lean_ctor_set(x_218, 3, x_204);
lean_ctor_set(x_218, 4, x_205);
x_219 = l_Array_isEmpty___rarg(x_215);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_218);
x_220 = lean_array_get_size(x_215);
lean_inc(x_2);
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_3);
lean_ctor_set(x_221, 1, x_2);
lean_ctor_set(x_221, 2, x_217);
lean_ctor_set(x_221, 3, x_215);
lean_ctor_set(x_221, 4, x_220);
x_222 = l_Lean_mkOptionalNode___closed__2;
x_223 = lean_array_push(x_222, x_4);
x_224 = l_Array_empty___closed__1;
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_array_push(x_203, x_221);
x_227 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_205, x_2, x_225);
if (lean_is_scalar(x_12)) {
 x_228 = lean_alloc_ctor(0, 5, 0);
} else {
 x_228 = x_12;
}
lean_ctor_set(x_228, 0, x_216);
lean_ctor_set(x_228, 1, x_202);
lean_ctor_set(x_228, 2, x_226);
lean_ctor_set(x_228, 3, x_204);
lean_ctor_set(x_228, 4, x_227);
x_229 = lean_box(0);
x_164 = x_229;
x_165 = x_228;
goto block_181;
}
else
{
lean_object* x_230; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_230 = lean_box(0);
x_164 = x_230;
x_165 = x_218;
goto block_181;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_231 = lean_ctor_get(x_214, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_214, 1);
lean_inc(x_232);
lean_dec(x_214);
if (lean_is_scalar(x_206)) {
 x_233 = lean_alloc_ctor(0, 5, 0);
} else {
 x_233 = x_206;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_202);
lean_ctor_set(x_233, 2, x_203);
lean_ctor_set(x_233, 3, x_204);
lean_ctor_set(x_233, 4, x_205);
x_182 = x_231;
x_183 = x_233;
goto block_199;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_234 = lean_ctor_get(x_207, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_207, 1);
lean_inc(x_235);
lean_dec(x_207);
if (lean_is_scalar(x_206)) {
 x_236 = lean_alloc_ctor(0, 5, 0);
} else {
 x_236 = x_206;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_202);
lean_ctor_set(x_236, 2, x_203);
lean_ctor_set(x_236, 3, x_204);
lean_ctor_set(x_236, 4, x_205);
x_182 = x_234;
x_183 = x_236;
goto block_199;
}
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Meta_SynthInstance_newSubgoal___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_eqv(x_4, x_1);
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 4);
lean_inc(x_4);
x_5 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_4, x_1);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find_x3f___main___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Meta_SynthInstance_findEntry_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_findEntry_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SynthInstance_SynthM_inhabited(lean_box(0));
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid key at synthInstance");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_getEntry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(231u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Meta_SynthInstance_getEntry___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_getEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_8 = l_Lean_Meta_SynthInstance_getEntry___closed__3;
x_9 = lean_panic_fn(x_7, x_8);
x_10 = lean_apply_2(x_9, x_2, x_6);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_getEntry(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_mkTableKeyFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_38; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
lean_ctor_set(x_6, 1, x_1);
lean_inc(x_3);
x_38 = l_Lean_Meta_inferType(x_2, x_3, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_instantiateMVars(x_39, x_3, x_40);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 1);
lean_dec(x_47);
lean_ctor_set(x_44, 1, x_8);
lean_ctor_set(x_4, 0, x_44);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 2);
x_50 = lean_ctor_get(x_44, 3);
x_51 = lean_ctor_get(x_44, 4);
x_52 = lean_ctor_get(x_44, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_8);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set(x_53, 5, x_52);
lean_ctor_set(x_4, 0, x_53);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_56 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 5);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 6, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_8);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_59);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_63, 5, x_61);
lean_ctor_set(x_4, 0, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_4);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
lean_dec(x_1);
x_65 = lean_ctor_get(x_38, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_38, 1);
lean_inc(x_66);
lean_dec(x_38);
lean_ctor_set(x_4, 0, x_66);
x_9 = x_65;
x_10 = x_4;
goto block_37;
}
block_37:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_dec(x_14);
lean_ctor_set(x_12, 1, x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 2);
x_18 = lean_ctor_get(x_12, 3);
x_19 = lean_ctor_get(x_12, 4);
x_20 = lean_ctor_get(x_12, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set(x_21, 5, x_20);
lean_ctor_set(x_10, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_10, 2);
x_26 = lean_ctor_get(x_10, 3);
x_27 = lean_ctor_get(x_10, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 x_33 = x_23;
} else {
 lean_dec_ref(x_23);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_91; lean_object* x_92; 
x_67 = lean_ctor_get(x_6, 0);
x_68 = lean_ctor_get(x_6, 1);
x_69 = lean_ctor_get(x_6, 2);
x_70 = lean_ctor_get(x_6, 3);
x_71 = lean_ctor_get(x_6, 4);
x_72 = lean_ctor_get(x_6, 5);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_6);
lean_inc(x_1);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_67);
lean_ctor_set(x_91, 1, x_1);
lean_ctor_set(x_91, 2, x_69);
lean_ctor_set(x_91, 3, x_70);
lean_ctor_set(x_91, 4, x_71);
lean_ctor_set(x_91, 5, x_72);
lean_inc(x_3);
x_92 = l_Lean_Meta_inferType(x_2, x_3, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Meta_instantiateMVars(x_93, x_3, x_94);
lean_dec(x_3);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_96);
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_97, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 5);
lean_inc(x_104);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 lean_ctor_release(x_97, 4);
 lean_ctor_release(x_97, 5);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 6, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_68);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_104);
lean_ctor_set(x_4, 0, x_106);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_4);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_3);
lean_dec(x_1);
x_108 = lean_ctor_get(x_92, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_dec(x_92);
lean_ctor_set(x_4, 0, x_109);
x_73 = x_108;
x_74 = x_4;
goto block_90;
}
block_90:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 4);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_75, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_75, 5);
lean_inc(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 6, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_68);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set(x_87, 4, x_84);
lean_ctor_set(x_87, 5, x_85);
if (lean_is_scalar(x_80)) {
 x_88 = lean_alloc_ctor(0, 5, 0);
} else {
 x_88 = x_80;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
lean_ctor_set(x_88, 2, x_77);
lean_ctor_set(x_88, 3, x_78);
lean_ctor_set(x_88, 4, x_79);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_73);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_140; lean_object* x_141; 
x_110 = lean_ctor_get(x_4, 0);
x_111 = lean_ctor_get(x_4, 1);
x_112 = lean_ctor_get(x_4, 2);
x_113 = lean_ctor_get(x_4, 3);
x_114 = lean_ctor_get(x_4, 4);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_4);
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_110, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_110, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_110, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 x_121 = x_110;
} else {
 lean_dec_ref(x_110);
 x_121 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_121)) {
 x_140 = lean_alloc_ctor(0, 6, 0);
} else {
 x_140 = x_121;
}
lean_ctor_set(x_140, 0, x_115);
lean_ctor_set(x_140, 1, x_1);
lean_ctor_set(x_140, 2, x_117);
lean_ctor_set(x_140, 3, x_118);
lean_ctor_set(x_140, 4, x_119);
lean_ctor_set(x_140, 5, x_120);
lean_inc(x_3);
x_141 = l_Lean_Meta_inferType(x_2, x_3, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Meta_instantiateMVars(x_142, x_3, x_143);
lean_dec(x_3);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Meta_SynthInstance_mkTableKey(x_1, x_145);
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_146, 5);
lean_inc(x_153);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 lean_ctor_release(x_146, 5);
 x_154 = x_146;
} else {
 lean_dec_ref(x_146);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 6, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set(x_155, 1, x_116);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_151);
lean_ctor_set(x_155, 4, x_152);
lean_ctor_set(x_155, 5, x_153);
x_156 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_111);
lean_ctor_set(x_156, 2, x_112);
lean_ctor_set(x_156, 3, x_113);
lean_ctor_set(x_156, 4, x_114);
if (lean_is_scalar(x_147)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_147;
}
lean_ctor_set(x_157, 0, x_148);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_3);
lean_dec(x_1);
x_158 = lean_ctor_get(x_141, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_141, 1);
lean_inc(x_159);
lean_dec(x_141);
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_111);
lean_ctor_set(x_160, 2, x_112);
lean_ctor_set(x_160, 3, x_113);
lean_ctor_set(x_160, 4, x_114);
x_122 = x_158;
x_123 = x_160;
goto block_139;
}
block_139:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 4);
lean_inc(x_128);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 x_129 = x_123;
} else {
 lean_dec_ref(x_123);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_124, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_124, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 5);
lean_inc(x_134);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_135 = x_124;
} else {
 lean_dec_ref(x_124);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 6, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_130);
lean_ctor_set(x_136, 1, x_116);
lean_ctor_set(x_136, 2, x_131);
lean_ctor_set(x_136, 3, x_132);
lean_ctor_set(x_136, 4, x_133);
lean_ctor_set(x_136, 5, x_134);
if (lean_is_scalar(x_129)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_129;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_125);
lean_ctor_set(x_137, 2, x_126);
lean_ctor_set(x_137, 3, x_127);
lean_ctor_set(x_137, 4, x_128);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_122);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_35 = lean_array_get_size(x_4);
x_36 = lean_expr_instantiate_rev_range(x_32, x_5, x_35, x_4);
lean_dec(x_35);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_3);
x_37 = l_Lean_Meta_mkForall(x_3, x_36, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkFreshExprMVarAt(x_1, x_2, x_38, x_40, x_41, x_9, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(0u);
lean_inc(x_43);
x_46 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_45, x_43);
lean_inc(x_46);
x_47 = l_Lean_mkApp(x_7, x_46);
x_48 = (uint8_t)((x_34 << 24) >> 61);
x_49 = l_Lean_BinderInfo_isInstImplicit(x_48);
x_50 = lean_array_push(x_4, x_46);
if (x_49 == 0)
{
lean_dec(x_43);
x_4 = x_50;
x_7 = x_47;
x_8 = x_33;
x_10 = x_44;
goto _start;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_6);
x_4 = x_50;
x_6 = x_52;
x_7 = x_47;
x_8 = x_33;
x_10 = x_44;
goto _start;
}
}
else
{
uint8_t x_54; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_37);
if (x_54 == 0)
{
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_37);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
x_58 = lean_box(0);
x_11 = x_58;
goto block_31;
}
block_31:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_12 = lean_array_get_size(x_4);
x_13 = lean_expr_instantiate_rev_range(x_8, x_5, x_12, x_4);
lean_dec(x_5);
lean_dec(x_8);
lean_inc(x_9);
x_14 = l_Lean_Meta_whnf(x_13, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Expr_isForall(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_free_object(x_14);
x_5 = x_12;
x_8 = x_16;
x_10 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = l_Lean_Expr_isForall(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
x_5 = x_12;
x_8 = x_21;
x_10 = x_22;
goto _start;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_SynthInstance_getSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Meta_inferType(x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = l_Array_empty___closed__1;
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_13 = l___private_Lean_Meta_SynthInstance_1__getSubgoalsAux___main(x_1, x_2, x_3, x_11, x_12, x_10, x_4, x_8, x_5, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_getAppFn___main(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_21 = l_Lean_TagAttribute_hasTag(x_20, x_19, x_18);
lean_dec(x_18);
lean_dec(x_19);
if (x_21 == 0)
{
return x_13;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = l_List_reverse___rarg(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_ctor_get(x_15, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_28 = l_List_reverse___rarg(x_25);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_13, 0, x_29);
return x_13;
}
}
}
else
{
lean_dec(x_17);
return x_13;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = l_Lean_Expr_getAppFn___main(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_32) == 4)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr;
x_36 = l_Lean_TagAttribute_hasTag(x_35, x_34, x_33);
lean_dec(x_33);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 2);
lean_inc(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
x_42 = l_List_reverse___rarg(x_38);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 3, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_32);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_31);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
return x_7;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tryResolve");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failure assigning");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_5);
x_9 = l_Lean_Meta_SynthInstance_getSubgoals(x_1, x_2, x_5, x_3, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_180; uint8_t x_181; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
lean_dec(x_10);
x_180 = lean_ctor_get(x_11, 4);
lean_inc(x_180);
x_181 = lean_ctor_get_uint8(x_180, sizeof(void*)*1);
lean_dec(x_180);
if (x_181 == 0)
{
x_15 = x_11;
goto block_179;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_183 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_182, x_7, x_11);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_15 = x_186;
goto block_179;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_dec(x_183);
lean_inc(x_6);
x_188 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_188, 0, x_6);
x_189 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_190 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_inc(x_14);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_14);
x_192 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_182, x_192, x_7, x_187);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_15 = x_194;
goto block_179;
}
}
block_179:
{
lean_object* x_16; 
lean_inc(x_7);
x_16 = l_Lean_Meta_isExprDefEq(x_6, x_14, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_ctor_get(x_20, 4);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_7);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_16);
x_25 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_26 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_25, x_7, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l_Lean_Meta_isLevelDefEq___closed__6;
x_35 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_25, x_34, x_7, x_33);
lean_dec(x_7);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_22);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_box(0);
x_42 = lean_ctor_get(x_40, 4);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_46 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_45, x_7, x_40);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_7);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = l_Lean_Meta_isLevelDefEq___closed__6;
x_54 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_45, x_53, x_7, x_52);
lean_dec(x_7);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_dec(x_16);
lean_inc(x_7);
x_59 = l_Lean_Meta_mkLambda(x_5, x_13, x_7, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_7);
x_62 = l_Lean_Meta_isExprDefEq(x_4, x_60, x_7, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_12);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_62, 1);
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = lean_box(0);
x_69 = lean_ctor_get(x_66, 4);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_69, sizeof(void*)*1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_dec(x_7);
lean_ctor_set(x_62, 0, x_68);
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_free_object(x_62);
x_71 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_72 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_71, x_7, x_66);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_7);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
lean_ctor_set(x_72, 0, x_68);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5;
x_81 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_71, x_80, x_7, x_79);
lean_dec(x_7);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_68);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_62, 1);
lean_inc(x_86);
lean_dec(x_62);
x_87 = lean_box(0);
x_88 = lean_ctor_get(x_86, 4);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_88, sizeof(void*)*1);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_7);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_92 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_91, x_7, x_86);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_7);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_dec(x_92);
x_99 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5;
x_100 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_91, x_99, x_7, x_98);
lean_dec(x_7);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_87);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_62);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_62, 1);
x_106 = lean_ctor_get(x_62, 0);
lean_dec(x_106);
x_107 = lean_ctor_get(x_105, 4);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_107, sizeof(void*)*1);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_7);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_12);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_62, 0, x_111);
return x_62;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_free_object(x_62);
x_112 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_113 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_112, x_7, x_105);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
uint8_t x_116; 
lean_dec(x_7);
x_116 = !lean_is_exclusive(x_113);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_113, 1);
x_118 = lean_ctor_get(x_113, 0);
lean_dec(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_12);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_113, 0, x_121);
return x_113;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_113, 1);
lean_inc(x_122);
lean_dec(x_113);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_12);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_113, 1);
lean_inc(x_127);
lean_dec(x_113);
x_128 = l_Lean_Meta_isLevelDefEq___closed__9;
x_129 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_112, x_128, x_7, x_127);
lean_dec(x_7);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_129, 1);
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_12);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_129, 0, x_135);
return x_129;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
lean_dec(x_129);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_12);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_62, 1);
lean_inc(x_141);
lean_dec(x_62);
x_142 = lean_ctor_get(x_141, 4);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_7);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_12);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_149 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_148, x_7, x_141);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_7);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_12);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_158 = lean_ctor_get(x_149, 1);
lean_inc(x_158);
lean_dec(x_149);
x_159 = l_Lean_Meta_isLevelDefEq___closed__9;
x_160 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_148, x_159, x_7, x_158);
lean_dec(x_7);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_12);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_161);
return x_166;
}
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_12);
lean_dec(x_7);
x_167 = !lean_is_exclusive(x_62);
if (x_167 == 0)
{
return x_62;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_62, 0);
x_169 = lean_ctor_get(x_62, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_62);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_4);
x_171 = !lean_is_exclusive(x_59);
if (x_171 == 0)
{
return x_59;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_59, 0);
x_173 = lean_ctor_get(x_59, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_59);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_175 = !lean_is_exclusive(x_16);
if (x_175 == 0)
{
return x_16;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_16, 0);
x_177 = lean_ctor_get(x_16, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_16);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_195 = !lean_is_exclusive(x_9);
if (x_195 == 0)
{
return x_9;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_9, 0);
x_197 = lean_ctor_get(x_9, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_9);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolveCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1), 8, 4);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_1);
x_11 = l_Lean_Meta_forallTelescopeReducing___rarg(x_6, x_10, x_3, x_7);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 4);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = l_PersistentArray_empty___closed__3;
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_18 = l_PersistentArray_empty___closed__3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_17);
lean_ctor_set(x_4, 4, x_19);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_ctor_get(x_4, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_26 = x_5;
} else {
 lean_dec_ref(x_5);
 x_26 = lean_box(0);
}
x_27 = l_PersistentArray_empty___closed__3;
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 1, 1);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_25);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_29, 5, x_24);
lean_ctor_set(x_3, 0, x_29);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_ctor_get(x_3, 3);
x_33 = lean_ctor_get(x_3, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 5);
lean_inc(x_38);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_39 = x_4;
} else {
 lean_dec_ref(x_4);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_41 = x_5;
} else {
 lean_dec_ref(x_5);
 x_41 = lean_box(0);
}
x_42 = l_PersistentArray_empty___closed__3;
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 1, 1);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_40);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 6, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_38);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
lean_ctor_set(x_45, 2, x_31);
lean_ctor_set(x_45, 3, x_32);
lean_ctor_set(x_45, 4, x_33);
lean_ctor_set(x_2, 1, x_45);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
lean_dec(x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 4);
lean_inc(x_51);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_52 = x_3;
} else {
 lean_dec_ref(x_3);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_4, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_4, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 5);
lean_inc(x_57);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_58 = x_4;
} else {
 lean_dec_ref(x_4);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_60 = x_5;
} else {
 lean_dec_ref(x_5);
 x_60 = lean_box(0);
}
x_61 = l_PersistentArray_empty___closed__3;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 1);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_59);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 6, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set(x_63, 2, x_55);
lean_ctor_set(x_63, 3, x_56);
lean_ctor_set(x_63, 4, x_62);
lean_ctor_set(x_63, 5, x_57);
if (lean_is_scalar(x_52)) {
 x_64 = lean_alloc_ctor(0, 5, 0);
} else {
 x_64 = x_52;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_48);
lean_ctor_set(x_64, 2, x_49);
lean_ctor_set(x_64, 3, x_50);
lean_ctor_set(x_64, 4, x_51);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_47);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 4);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = l_PersistentArray_toArray___rarg(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_PersistentArray_push___rarg(x_1, x_15);
lean_ctor_set(x_6, 0, x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = l_PersistentArray_toArray___rarg(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_PersistentArray_push___rarg(x_1, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_19);
lean_ctor_set(x_5, 4, x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_35 = x_6;
} else {
 lean_dec_ref(x_6);
 x_35 = lean_box(0);
}
x_36 = l_PersistentArray_toArray___rarg(x_34);
lean_dec(x_34);
x_37 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_PersistentArray_push___rarg(x_1, x_38);
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(0, 1, 1);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_33);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_32);
lean_ctor_set(x_4, 0, x_41);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_4);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_4, 1);
x_45 = lean_ctor_get(x_4, 2);
x_46 = lean_ctor_get(x_4, 3);
x_47 = lean_ctor_get(x_4, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_4);
x_48 = lean_ctor_get(x_5, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_5, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_5, 5);
lean_inc(x_52);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_53 = x_5;
} else {
 lean_dec_ref(x_5);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_56 = x_6;
} else {
 lean_dec_ref(x_6);
 x_56 = lean_box(0);
}
x_57 = l_PersistentArray_toArray___rarg(x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_PersistentArray_push___rarg(x_1, x_59);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 1, 1);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_54);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_53;
}
lean_ctor_set(x_62, 0, x_48);
lean_ctor_set(x_62, 1, x_49);
lean_ctor_set(x_62, 2, x_50);
lean_ctor_set(x_62, 3, x_51);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_52);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_46);
lean_ctor_set(x_63, 4, x_47);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_tryResolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_540 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_5);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get_uint8(x_541, sizeof(void*)*1);
lean_dec(x_541);
if (x_542 == 0)
{
lean_object* x_543; uint8_t x_544; 
x_543 = lean_ctor_get(x_540, 1);
lean_inc(x_543);
lean_dec(x_540);
x_544 = 0;
x_6 = x_544;
x_7 = x_543;
goto block_539;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; 
x_545 = lean_ctor_get(x_540, 1);
lean_inc(x_545);
lean_dec(x_540);
x_546 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_547 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_546, x_4, x_545);
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
x_550 = lean_unbox(x_548);
lean_dec(x_548);
x_6 = x_550;
x_7 = x_549;
goto block_539;
}
block_539:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_8 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 4);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_81; 
x_20 = 0;
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_20);
lean_ctor_set(x_11, 1, x_1);
x_81 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 1);
lean_dec(x_85);
lean_ctor_set(x_82, 1, x_17);
lean_ctor_set(x_10, 0, x_82);
x_86 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_10);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_86, 1);
x_89 = lean_ctor_get(x_86, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 4);
lean_inc(x_91);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_88, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_90, 4);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_13);
lean_ctor_set(x_86, 0, x_83);
return x_86;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_91, 0);
lean_inc(x_97);
lean_dec(x_91);
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_13);
lean_ctor_set(x_90, 4, x_98);
lean_ctor_set(x_86, 0, x_83);
return x_86;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_99 = lean_ctor_get(x_90, 0);
x_100 = lean_ctor_get(x_90, 1);
x_101 = lean_ctor_get(x_90, 2);
x_102 = lean_ctor_get(x_90, 3);
x_103 = lean_ctor_get(x_90, 5);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_90);
x_104 = lean_ctor_get(x_91, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_105 = x_91;
} else {
 lean_dec_ref(x_91);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 1, 1);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_13);
x_107 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_107, 2, x_101);
lean_ctor_set(x_107, 3, x_102);
lean_ctor_set(x_107, 4, x_106);
lean_ctor_set(x_107, 5, x_103);
lean_ctor_set(x_88, 0, x_107);
lean_ctor_set(x_86, 0, x_83);
return x_86;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_108 = lean_ctor_get(x_88, 1);
x_109 = lean_ctor_get(x_88, 2);
x_110 = lean_ctor_get(x_88, 3);
x_111 = lean_ctor_get(x_88, 4);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_88);
x_112 = lean_ctor_get(x_90, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_90, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_90, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_90, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_90, 5);
lean_inc(x_116);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 lean_ctor_release(x_90, 5);
 x_117 = x_90;
} else {
 lean_dec_ref(x_90);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_91, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_119 = x_91;
} else {
 lean_dec_ref(x_91);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 1, 1);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 6, 0);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_113);
lean_ctor_set(x_121, 2, x_114);
lean_ctor_set(x_121, 3, x_115);
lean_ctor_set(x_121, 4, x_120);
lean_ctor_set(x_121, 5, x_116);
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_108);
lean_ctor_set(x_122, 2, x_109);
lean_ctor_set(x_122, 3, x_110);
lean_ctor_set(x_122, 4, x_111);
lean_ctor_set(x_86, 1, x_122);
lean_ctor_set(x_86, 0, x_83);
return x_86;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_123 = lean_ctor_get(x_86, 1);
lean_inc(x_123);
lean_dec(x_86);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 4);
lean_inc(x_129);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 x_130 = x_123;
} else {
 lean_dec_ref(x_123);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_124, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_124, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 5);
lean_inc(x_135);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_136 = x_124;
} else {
 lean_dec_ref(x_124);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_125, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_138 = x_125;
} else {
 lean_dec_ref(x_125);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 1, 1);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_136)) {
 x_140 = lean_alloc_ctor(0, 6, 0);
} else {
 x_140 = x_136;
}
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_133);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_139);
lean_ctor_set(x_140, 5, x_135);
if (lean_is_scalar(x_130)) {
 x_141 = lean_alloc_ctor(0, 5, 0);
} else {
 x_141 = x_130;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
lean_ctor_set(x_141, 2, x_127);
lean_ctor_set(x_141, 3, x_128);
lean_ctor_set(x_141, 4, x_129);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_83);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_143 = lean_ctor_get(x_82, 0);
x_144 = lean_ctor_get(x_82, 2);
x_145 = lean_ctor_get(x_82, 3);
x_146 = lean_ctor_get(x_82, 4);
x_147 = lean_ctor_get(x_82, 5);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_82);
x_148 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_17);
lean_ctor_set(x_148, 2, x_144);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set(x_148, 4, x_146);
lean_ctor_set(x_148, 5, x_147);
lean_ctor_set(x_10, 0, x_148);
x_149 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_10);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_152, 4);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_150, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_150, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_150, 4);
lean_inc(x_157);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 lean_ctor_release(x_150, 3);
 lean_ctor_release(x_150, 4);
 x_158 = x_150;
} else {
 lean_dec_ref(x_150);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_152, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_152, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_152, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_152, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_152, 5);
lean_inc(x_163);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 lean_ctor_release(x_152, 5);
 x_164 = x_152;
} else {
 lean_dec_ref(x_152);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_153, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_166 = x_153;
} else {
 lean_dec_ref(x_153);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 1, 1);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_164)) {
 x_168 = lean_alloc_ctor(0, 6, 0);
} else {
 x_168 = x_164;
}
lean_ctor_set(x_168, 0, x_159);
lean_ctor_set(x_168, 1, x_160);
lean_ctor_set(x_168, 2, x_161);
lean_ctor_set(x_168, 3, x_162);
lean_ctor_set(x_168, 4, x_167);
lean_ctor_set(x_168, 5, x_163);
if (lean_is_scalar(x_158)) {
 x_169 = lean_alloc_ctor(0, 5, 0);
} else {
 x_169 = x_158;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_154);
lean_ctor_set(x_169, 2, x_155);
lean_ctor_set(x_169, 3, x_156);
lean_ctor_set(x_169, 4, x_157);
if (lean_is_scalar(x_151)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_151;
}
lean_ctor_set(x_170, 0, x_83);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_81, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_81, 0);
lean_inc(x_172);
lean_dec(x_81);
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_171, 1);
lean_dec(x_174);
lean_ctor_set(x_171, 1, x_17);
lean_ctor_set(x_10, 0, x_171);
x_21 = x_172;
x_22 = x_10;
goto block_80;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_171, 0);
x_176 = lean_ctor_get(x_171, 2);
x_177 = lean_ctor_get(x_171, 3);
x_178 = lean_ctor_get(x_171, 4);
x_179 = lean_ctor_get(x_171, 5);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_171);
x_180 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_17);
lean_ctor_set(x_180, 2, x_176);
lean_ctor_set(x_180, 3, x_177);
lean_ctor_set(x_180, 4, x_178);
lean_ctor_set(x_180, 5, x_179);
lean_ctor_set(x_10, 0, x_180);
x_21 = x_172;
x_22 = x_10;
goto block_80;
}
}
block_80:
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_27, 4);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_13);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_13);
lean_ctor_set(x_27, 4, x_35);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
x_38 = lean_ctor_get(x_27, 2);
x_39 = lean_ctor_get(x_27, 3);
x_40 = lean_ctor_get(x_27, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 1, 1);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_13);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_25, 0, x_44);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_25, 1);
x_46 = lean_ctor_get(x_25, 2);
x_47 = lean_ctor_get(x_25, 3);
x_48 = lean_ctor_get(x_25, 4);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_49 = lean_ctor_get(x_27, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_27, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_27, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_27, 5);
lean_inc(x_53);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 x_54 = x_27;
} else {
 lean_dec_ref(x_27);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_28, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_56 = x_28;
} else {
 lean_dec_ref(x_28);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 1);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_52);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_53);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_45);
lean_ctor_set(x_59, 2, x_46);
lean_ctor_set(x_59, 3, x_47);
lean_ctor_set(x_59, 4, x_48);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_59);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_60 = lean_ctor_get(x_23, 1);
lean_inc(x_60);
lean_dec(x_23);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 4);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 5);
lean_inc(x_72);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 x_73 = x_61;
} else {
 lean_dec_ref(x_61);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_62, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_71);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_72);
if (lean_is_scalar(x_67)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_67;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_63);
lean_ctor_set(x_78, 2, x_64);
lean_ctor_set(x_78, 3, x_65);
lean_ctor_set(x_78, 4, x_66);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_21);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_209; 
x_181 = lean_ctor_get(x_12, 0);
lean_inc(x_181);
lean_dec(x_12);
x_182 = 0;
x_183 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*1, x_182);
lean_ctor_set(x_11, 4, x_183);
lean_ctor_set(x_11, 1, x_1);
x_209 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 2);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 3);
lean_inc(x_214);
x_215 = lean_ctor_get(x_210, 4);
lean_inc(x_215);
x_216 = lean_ctor_get(x_210, 5);
lean_inc(x_216);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 lean_ctor_release(x_210, 4);
 lean_ctor_release(x_210, 5);
 x_217 = x_210;
} else {
 lean_dec_ref(x_210);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 6, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_212);
lean_ctor_set(x_218, 1, x_17);
lean_ctor_set(x_218, 2, x_213);
lean_ctor_set(x_218, 3, x_214);
lean_ctor_set(x_218, 4, x_215);
lean_ctor_set(x_218, 5, x_216);
lean_ctor_set(x_10, 0, x_218);
x_219 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_10);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 4);
lean_inc(x_223);
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_220, 4);
lean_inc(x_227);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 lean_ctor_release(x_220, 2);
 lean_ctor_release(x_220, 3);
 lean_ctor_release(x_220, 4);
 x_228 = x_220;
} else {
 lean_dec_ref(x_220);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_222, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_222, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_222, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_222, 3);
lean_inc(x_232);
x_233 = lean_ctor_get(x_222, 5);
lean_inc(x_233);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 lean_ctor_release(x_222, 3);
 lean_ctor_release(x_222, 4);
 lean_ctor_release(x_222, 5);
 x_234 = x_222;
} else {
 lean_dec_ref(x_222);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_223, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_236 = x_223;
} else {
 lean_dec_ref(x_223);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(0, 1, 1);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set_uint8(x_237, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_234)) {
 x_238 = lean_alloc_ctor(0, 6, 0);
} else {
 x_238 = x_234;
}
lean_ctor_set(x_238, 0, x_229);
lean_ctor_set(x_238, 1, x_230);
lean_ctor_set(x_238, 2, x_231);
lean_ctor_set(x_238, 3, x_232);
lean_ctor_set(x_238, 4, x_237);
lean_ctor_set(x_238, 5, x_233);
if (lean_is_scalar(x_228)) {
 x_239 = lean_alloc_ctor(0, 5, 0);
} else {
 x_239 = x_228;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_224);
lean_ctor_set(x_239, 2, x_225);
lean_ctor_set(x_239, 3, x_226);
lean_ctor_set(x_239, 4, x_227);
if (lean_is_scalar(x_221)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_221;
}
lean_ctor_set(x_240, 0, x_211);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_241 = lean_ctor_get(x_209, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_209, 0);
lean_inc(x_242);
lean_dec(x_209);
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_241, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_241, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_241, 5);
lean_inc(x_247);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 lean_ctor_release(x_241, 4);
 lean_ctor_release(x_241, 5);
 x_248 = x_241;
} else {
 lean_dec_ref(x_241);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(0, 6, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_243);
lean_ctor_set(x_249, 1, x_17);
lean_ctor_set(x_249, 2, x_244);
lean_ctor_set(x_249, 3, x_245);
lean_ctor_set(x_249, 4, x_246);
lean_ctor_set(x_249, 5, x_247);
lean_ctor_set(x_10, 0, x_249);
x_184 = x_242;
x_185 = x_10;
goto block_208;
}
block_208:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_186 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_185);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_189, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_187, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_187, 4);
lean_inc(x_194);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 lean_ctor_release(x_187, 4);
 x_195 = x_187;
} else {
 lean_dec_ref(x_187);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_189, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_189, 5);
lean_inc(x_200);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 x_201 = x_189;
} else {
 lean_dec_ref(x_189);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_190, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_203 = x_190;
} else {
 lean_dec_ref(x_190);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 1, 1);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_201)) {
 x_205 = lean_alloc_ctor(0, 6, 0);
} else {
 x_205 = x_201;
}
lean_ctor_set(x_205, 0, x_196);
lean_ctor_set(x_205, 1, x_197);
lean_ctor_set(x_205, 2, x_198);
lean_ctor_set(x_205, 3, x_199);
lean_ctor_set(x_205, 4, x_204);
lean_ctor_set(x_205, 5, x_200);
if (lean_is_scalar(x_195)) {
 x_206 = lean_alloc_ctor(0, 5, 0);
} else {
 x_206 = x_195;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_191);
lean_ctor_set(x_206, 2, x_192);
lean_ctor_set(x_206, 3, x_193);
lean_ctor_set(x_206, 4, x_194);
if (lean_is_scalar(x_188)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_188;
 lean_ctor_set_tag(x_207, 1);
}
lean_ctor_set(x_207, 0, x_184);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_284; lean_object* x_285; 
x_250 = lean_ctor_get(x_11, 0);
x_251 = lean_ctor_get(x_11, 1);
x_252 = lean_ctor_get(x_11, 2);
x_253 = lean_ctor_get(x_11, 3);
x_254 = lean_ctor_get(x_11, 5);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_11);
x_255 = lean_ctor_get(x_12, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_256 = x_12;
} else {
 lean_dec_ref(x_12);
 x_256 = lean_box(0);
}
x_257 = 0;
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(0, 1, 1);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set_uint8(x_258, sizeof(void*)*1, x_257);
x_284 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_284, 0, x_250);
lean_ctor_set(x_284, 1, x_1);
lean_ctor_set(x_284, 2, x_252);
lean_ctor_set(x_284, 3, x_253);
lean_ctor_set(x_284, 4, x_258);
lean_ctor_set(x_284, 5, x_254);
x_285 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 0);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 2);
lean_inc(x_289);
x_290 = lean_ctor_get(x_286, 3);
lean_inc(x_290);
x_291 = lean_ctor_get(x_286, 4);
lean_inc(x_291);
x_292 = lean_ctor_get(x_286, 5);
lean_inc(x_292);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 lean_ctor_release(x_286, 2);
 lean_ctor_release(x_286, 3);
 lean_ctor_release(x_286, 4);
 lean_ctor_release(x_286, 5);
 x_293 = x_286;
} else {
 lean_dec_ref(x_286);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(0, 6, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_251);
lean_ctor_set(x_294, 2, x_289);
lean_ctor_set(x_294, 3, x_290);
lean_ctor_set(x_294, 4, x_291);
lean_ctor_set(x_294, 5, x_292);
lean_ctor_set(x_10, 0, x_294);
x_295 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_10);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_297 = x_295;
} else {
 lean_dec_ref(x_295);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_298, 4);
lean_inc(x_299);
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_296, 2);
lean_inc(x_301);
x_302 = lean_ctor_get(x_296, 3);
lean_inc(x_302);
x_303 = lean_ctor_get(x_296, 4);
lean_inc(x_303);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 lean_ctor_release(x_296, 2);
 lean_ctor_release(x_296, 3);
 lean_ctor_release(x_296, 4);
 x_304 = x_296;
} else {
 lean_dec_ref(x_296);
 x_304 = lean_box(0);
}
x_305 = lean_ctor_get(x_298, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_298, 1);
lean_inc(x_306);
x_307 = lean_ctor_get(x_298, 2);
lean_inc(x_307);
x_308 = lean_ctor_get(x_298, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_298, 5);
lean_inc(x_309);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 lean_ctor_release(x_298, 4);
 lean_ctor_release(x_298, 5);
 x_310 = x_298;
} else {
 lean_dec_ref(x_298);
 x_310 = lean_box(0);
}
x_311 = lean_ctor_get(x_299, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 x_312 = x_299;
} else {
 lean_dec_ref(x_299);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 1, 1);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set_uint8(x_313, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_310)) {
 x_314 = lean_alloc_ctor(0, 6, 0);
} else {
 x_314 = x_310;
}
lean_ctor_set(x_314, 0, x_305);
lean_ctor_set(x_314, 1, x_306);
lean_ctor_set(x_314, 2, x_307);
lean_ctor_set(x_314, 3, x_308);
lean_ctor_set(x_314, 4, x_313);
lean_ctor_set(x_314, 5, x_309);
if (lean_is_scalar(x_304)) {
 x_315 = lean_alloc_ctor(0, 5, 0);
} else {
 x_315 = x_304;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_300);
lean_ctor_set(x_315, 2, x_301);
lean_ctor_set(x_315, 3, x_302);
lean_ctor_set(x_315, 4, x_303);
if (lean_is_scalar(x_297)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_297;
}
lean_ctor_set(x_316, 0, x_287);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_317 = lean_ctor_get(x_285, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_285, 0);
lean_inc(x_318);
lean_dec(x_285);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_317, 3);
lean_inc(x_321);
x_322 = lean_ctor_get(x_317, 4);
lean_inc(x_322);
x_323 = lean_ctor_get(x_317, 5);
lean_inc(x_323);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 lean_ctor_release(x_317, 2);
 lean_ctor_release(x_317, 3);
 lean_ctor_release(x_317, 4);
 lean_ctor_release(x_317, 5);
 x_324 = x_317;
} else {
 lean_dec_ref(x_317);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(0, 6, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_319);
lean_ctor_set(x_325, 1, x_251);
lean_ctor_set(x_325, 2, x_320);
lean_ctor_set(x_325, 3, x_321);
lean_ctor_set(x_325, 4, x_322);
lean_ctor_set(x_325, 5, x_323);
lean_ctor_set(x_10, 0, x_325);
x_259 = x_318;
x_260 = x_10;
goto block_283;
}
block_283:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_261 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_260);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_264, 4);
lean_inc(x_265);
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_262, 2);
lean_inc(x_267);
x_268 = lean_ctor_get(x_262, 3);
lean_inc(x_268);
x_269 = lean_ctor_get(x_262, 4);
lean_inc(x_269);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 lean_ctor_release(x_262, 3);
 lean_ctor_release(x_262, 4);
 x_270 = x_262;
} else {
 lean_dec_ref(x_262);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_264, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_264, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_264, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_264, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_264, 5);
lean_inc(x_275);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 lean_ctor_release(x_264, 2);
 lean_ctor_release(x_264, 3);
 lean_ctor_release(x_264, 4);
 lean_ctor_release(x_264, 5);
 x_276 = x_264;
} else {
 lean_dec_ref(x_264);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_265, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_278 = x_265;
} else {
 lean_dec_ref(x_265);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 1, 1);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set_uint8(x_279, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_276)) {
 x_280 = lean_alloc_ctor(0, 6, 0);
} else {
 x_280 = x_276;
}
lean_ctor_set(x_280, 0, x_271);
lean_ctor_set(x_280, 1, x_272);
lean_ctor_set(x_280, 2, x_273);
lean_ctor_set(x_280, 3, x_274);
lean_ctor_set(x_280, 4, x_279);
lean_ctor_set(x_280, 5, x_275);
if (lean_is_scalar(x_270)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_270;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_266);
lean_ctor_set(x_281, 2, x_267);
lean_ctor_set(x_281, 3, x_268);
lean_ctor_set(x_281, 4, x_269);
if (lean_is_scalar(x_263)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_263;
 lean_ctor_set_tag(x_282, 1);
}
lean_ctor_set(x_282, 0, x_259);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_365; lean_object* x_366; 
x_326 = lean_ctor_get(x_10, 1);
x_327 = lean_ctor_get(x_10, 2);
x_328 = lean_ctor_get(x_10, 3);
x_329 = lean_ctor_get(x_10, 4);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_10);
x_330 = lean_ctor_get(x_11, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_11, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_11, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_11, 3);
lean_inc(x_333);
x_334 = lean_ctor_get(x_11, 5);
lean_inc(x_334);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_335 = x_11;
} else {
 lean_dec_ref(x_11);
 x_335 = lean_box(0);
}
x_336 = lean_ctor_get(x_12, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_337 = x_12;
} else {
 lean_dec_ref(x_12);
 x_337 = lean_box(0);
}
x_338 = 0;
if (lean_is_scalar(x_337)) {
 x_339 = lean_alloc_ctor(0, 1, 1);
} else {
 x_339 = x_337;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set_uint8(x_339, sizeof(void*)*1, x_338);
if (lean_is_scalar(x_335)) {
 x_365 = lean_alloc_ctor(0, 6, 0);
} else {
 x_365 = x_335;
}
lean_ctor_set(x_365, 0, x_330);
lean_ctor_set(x_365, 1, x_1);
lean_ctor_set(x_365, 2, x_332);
lean_ctor_set(x_365, 3, x_333);
lean_ctor_set(x_365, 4, x_339);
lean_ctor_set(x_365, 5, x_334);
x_366 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_365);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 0);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_367, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_367, 3);
lean_inc(x_371);
x_372 = lean_ctor_get(x_367, 4);
lean_inc(x_372);
x_373 = lean_ctor_get(x_367, 5);
lean_inc(x_373);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 lean_ctor_release(x_367, 4);
 lean_ctor_release(x_367, 5);
 x_374 = x_367;
} else {
 lean_dec_ref(x_367);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(0, 6, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_369);
lean_ctor_set(x_375, 1, x_331);
lean_ctor_set(x_375, 2, x_370);
lean_ctor_set(x_375, 3, x_371);
lean_ctor_set(x_375, 4, x_372);
lean_ctor_set(x_375, 5, x_373);
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_326);
lean_ctor_set(x_376, 2, x_327);
lean_ctor_set(x_376, 3, x_328);
lean_ctor_set(x_376, 4, x_329);
x_377 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_376);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_378, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_380, 4);
lean_inc(x_381);
x_382 = lean_ctor_get(x_378, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_378, 2);
lean_inc(x_383);
x_384 = lean_ctor_get(x_378, 3);
lean_inc(x_384);
x_385 = lean_ctor_get(x_378, 4);
lean_inc(x_385);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 lean_ctor_release(x_378, 4);
 x_386 = x_378;
} else {
 lean_dec_ref(x_378);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_380, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_380, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_380, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_380, 3);
lean_inc(x_390);
x_391 = lean_ctor_get(x_380, 5);
lean_inc(x_391);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 lean_ctor_release(x_380, 2);
 lean_ctor_release(x_380, 3);
 lean_ctor_release(x_380, 4);
 lean_ctor_release(x_380, 5);
 x_392 = x_380;
} else {
 lean_dec_ref(x_380);
 x_392 = lean_box(0);
}
x_393 = lean_ctor_get(x_381, 0);
lean_inc(x_393);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_394 = x_381;
} else {
 lean_dec_ref(x_381);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(0, 1, 1);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set_uint8(x_395, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_392)) {
 x_396 = lean_alloc_ctor(0, 6, 0);
} else {
 x_396 = x_392;
}
lean_ctor_set(x_396, 0, x_387);
lean_ctor_set(x_396, 1, x_388);
lean_ctor_set(x_396, 2, x_389);
lean_ctor_set(x_396, 3, x_390);
lean_ctor_set(x_396, 4, x_395);
lean_ctor_set(x_396, 5, x_391);
if (lean_is_scalar(x_386)) {
 x_397 = lean_alloc_ctor(0, 5, 0);
} else {
 x_397 = x_386;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_382);
lean_ctor_set(x_397, 2, x_383);
lean_ctor_set(x_397, 3, x_384);
lean_ctor_set(x_397, 4, x_385);
if (lean_is_scalar(x_379)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_379;
}
lean_ctor_set(x_398, 0, x_368);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_399 = lean_ctor_get(x_366, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_366, 0);
lean_inc(x_400);
lean_dec(x_366);
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_399, 2);
lean_inc(x_402);
x_403 = lean_ctor_get(x_399, 3);
lean_inc(x_403);
x_404 = lean_ctor_get(x_399, 4);
lean_inc(x_404);
x_405 = lean_ctor_get(x_399, 5);
lean_inc(x_405);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 lean_ctor_release(x_399, 2);
 lean_ctor_release(x_399, 3);
 lean_ctor_release(x_399, 4);
 lean_ctor_release(x_399, 5);
 x_406 = x_399;
} else {
 lean_dec_ref(x_399);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(0, 6, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_401);
lean_ctor_set(x_407, 1, x_331);
lean_ctor_set(x_407, 2, x_402);
lean_ctor_set(x_407, 3, x_403);
lean_ctor_set(x_407, 4, x_404);
lean_ctor_set(x_407, 5, x_405);
x_408 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_326);
lean_ctor_set(x_408, 2, x_327);
lean_ctor_set(x_408, 3, x_328);
lean_ctor_set(x_408, 4, x_329);
x_340 = x_400;
x_341 = x_408;
goto block_364;
}
block_364:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_342 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_341);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_344 = x_342;
} else {
 lean_dec_ref(x_342);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 4);
lean_inc(x_346);
x_347 = lean_ctor_get(x_343, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_343, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_343, 3);
lean_inc(x_349);
x_350 = lean_ctor_get(x_343, 4);
lean_inc(x_350);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 lean_ctor_release(x_343, 4);
 x_351 = x_343;
} else {
 lean_dec_ref(x_343);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_345, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_345, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_345, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_345, 3);
lean_inc(x_355);
x_356 = lean_ctor_get(x_345, 5);
lean_inc(x_356);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_357 = x_345;
} else {
 lean_dec_ref(x_345);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_346, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_359 = x_346;
} else {
 lean_dec_ref(x_346);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(0, 1, 1);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set_uint8(x_360, sizeof(void*)*1, x_13);
if (lean_is_scalar(x_357)) {
 x_361 = lean_alloc_ctor(0, 6, 0);
} else {
 x_361 = x_357;
}
lean_ctor_set(x_361, 0, x_352);
lean_ctor_set(x_361, 1, x_353);
lean_ctor_set(x_361, 2, x_354);
lean_ctor_set(x_361, 3, x_355);
lean_ctor_set(x_361, 4, x_360);
lean_ctor_set(x_361, 5, x_356);
if (lean_is_scalar(x_351)) {
 x_362 = lean_alloc_ctor(0, 5, 0);
} else {
 x_362 = x_351;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_347);
lean_ctor_set(x_362, 2, x_348);
lean_ctor_set(x_362, 3, x_349);
lean_ctor_set(x_362, 4, x_350);
if (lean_is_scalar(x_344)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_344;
 lean_ctor_set_tag(x_363, 1);
}
lean_ctor_set(x_363, 0, x_340);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_409 = l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_7);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_409, 0);
lean_inc(x_412);
lean_dec(x_409);
x_413 = !lean_is_exclusive(x_410);
if (x_413 == 0)
{
lean_object* x_414; uint8_t x_415; 
x_414 = lean_ctor_get(x_410, 0);
lean_dec(x_414);
x_415 = !lean_is_exclusive(x_411);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_411, 1);
lean_ctor_set(x_411, 1, x_1);
lean_inc(x_4);
x_417 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_411);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_419);
lean_dec(x_417);
x_420 = !lean_is_exclusive(x_418);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_421 = lean_ctor_get(x_418, 1);
lean_dec(x_421);
lean_ctor_set(x_418, 1, x_416);
lean_ctor_set(x_410, 0, x_418);
x_422 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_423 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_412, x_422, x_4, x_410);
lean_dec(x_4);
x_424 = !lean_is_exclusive(x_423);
if (x_424 == 0)
{
lean_object* x_425; 
x_425 = lean_ctor_get(x_423, 0);
lean_dec(x_425);
lean_ctor_set(x_423, 0, x_419);
return x_423;
}
else
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_dec(x_423);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_419);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_428 = lean_ctor_get(x_418, 0);
x_429 = lean_ctor_get(x_418, 2);
x_430 = lean_ctor_get(x_418, 3);
x_431 = lean_ctor_get(x_418, 4);
x_432 = lean_ctor_get(x_418, 5);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_418);
x_433 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_433, 0, x_428);
lean_ctor_set(x_433, 1, x_416);
lean_ctor_set(x_433, 2, x_429);
lean_ctor_set(x_433, 3, x_430);
lean_ctor_set(x_433, 4, x_431);
lean_ctor_set(x_433, 5, x_432);
lean_ctor_set(x_410, 0, x_433);
x_434 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_435 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_412, x_434, x_4, x_410);
lean_dec(x_4);
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_437 = x_435;
} else {
 lean_dec_ref(x_435);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_419);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
}
else
{
lean_object* x_439; lean_object* x_440; uint8_t x_441; 
x_439 = lean_ctor_get(x_417, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_417, 0);
lean_inc(x_440);
lean_dec(x_417);
x_441 = !lean_is_exclusive(x_439);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_442 = lean_ctor_get(x_439, 1);
lean_dec(x_442);
lean_ctor_set(x_439, 1, x_416);
lean_ctor_set(x_410, 0, x_439);
x_443 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_444 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_412, x_443, x_4, x_410);
lean_dec(x_4);
x_445 = !lean_is_exclusive(x_444);
if (x_445 == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_444, 0);
lean_dec(x_446);
lean_ctor_set_tag(x_444, 1);
lean_ctor_set(x_444, 0, x_440);
return x_444;
}
else
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_444, 1);
lean_inc(x_447);
lean_dec(x_444);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_440);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_449 = lean_ctor_get(x_439, 0);
x_450 = lean_ctor_get(x_439, 2);
x_451 = lean_ctor_get(x_439, 3);
x_452 = lean_ctor_get(x_439, 4);
x_453 = lean_ctor_get(x_439, 5);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_439);
x_454 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_416);
lean_ctor_set(x_454, 2, x_450);
lean_ctor_set(x_454, 3, x_451);
lean_ctor_set(x_454, 4, x_452);
lean_ctor_set(x_454, 5, x_453);
lean_ctor_set(x_410, 0, x_454);
x_455 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_456 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_412, x_455, x_4, x_410);
lean_dec(x_4);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_458;
 lean_ctor_set_tag(x_459, 1);
}
lean_ctor_set(x_459, 0, x_440);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_460 = lean_ctor_get(x_411, 0);
x_461 = lean_ctor_get(x_411, 1);
x_462 = lean_ctor_get(x_411, 2);
x_463 = lean_ctor_get(x_411, 3);
x_464 = lean_ctor_get(x_411, 4);
x_465 = lean_ctor_get(x_411, 5);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_411);
x_466 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_466, 0, x_460);
lean_ctor_set(x_466, 1, x_1);
lean_ctor_set(x_466, 2, x_462);
lean_ctor_set(x_466, 3, x_463);
lean_ctor_set(x_466, 4, x_464);
lean_ctor_set(x_466, 5, x_465);
lean_inc(x_4);
x_467 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_466);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_468 = lean_ctor_get(x_467, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 0);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_ctor_get(x_468, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_468, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_468, 3);
lean_inc(x_472);
x_473 = lean_ctor_get(x_468, 4);
lean_inc(x_473);
x_474 = lean_ctor_get(x_468, 5);
lean_inc(x_474);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 lean_ctor_release(x_468, 2);
 lean_ctor_release(x_468, 3);
 lean_ctor_release(x_468, 4);
 lean_ctor_release(x_468, 5);
 x_475 = x_468;
} else {
 lean_dec_ref(x_468);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(0, 6, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_470);
lean_ctor_set(x_476, 1, x_461);
lean_ctor_set(x_476, 2, x_471);
lean_ctor_set(x_476, 3, x_472);
lean_ctor_set(x_476, 4, x_473);
lean_ctor_set(x_476, 5, x_474);
lean_ctor_set(x_410, 0, x_476);
x_477 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_478 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_412, x_477, x_4, x_410);
lean_dec(x_4);
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_480 = x_478;
} else {
 lean_dec_ref(x_478);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_469);
lean_ctor_set(x_481, 1, x_479);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_482 = lean_ctor_get(x_467, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_467, 0);
lean_inc(x_483);
lean_dec(x_467);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_482, 2);
lean_inc(x_485);
x_486 = lean_ctor_get(x_482, 3);
lean_inc(x_486);
x_487 = lean_ctor_get(x_482, 4);
lean_inc(x_487);
x_488 = lean_ctor_get(x_482, 5);
lean_inc(x_488);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 lean_ctor_release(x_482, 2);
 lean_ctor_release(x_482, 3);
 lean_ctor_release(x_482, 4);
 lean_ctor_release(x_482, 5);
 x_489 = x_482;
} else {
 lean_dec_ref(x_482);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(0, 6, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_484);
lean_ctor_set(x_490, 1, x_461);
lean_ctor_set(x_490, 2, x_485);
lean_ctor_set(x_490, 3, x_486);
lean_ctor_set(x_490, 4, x_487);
lean_ctor_set(x_490, 5, x_488);
lean_ctor_set(x_410, 0, x_490);
x_491 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_492 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_412, x_491, x_4, x_410);
lean_dec(x_4);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_494 = x_492;
} else {
 lean_dec_ref(x_492);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_494;
 lean_ctor_set_tag(x_495, 1);
}
lean_ctor_set(x_495, 0, x_483);
lean_ctor_set(x_495, 1, x_493);
return x_495;
}
}
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_496 = lean_ctor_get(x_410, 1);
x_497 = lean_ctor_get(x_410, 2);
x_498 = lean_ctor_get(x_410, 3);
x_499 = lean_ctor_get(x_410, 4);
lean_inc(x_499);
lean_inc(x_498);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_410);
x_500 = lean_ctor_get(x_411, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_411, 1);
lean_inc(x_501);
x_502 = lean_ctor_get(x_411, 2);
lean_inc(x_502);
x_503 = lean_ctor_get(x_411, 3);
lean_inc(x_503);
x_504 = lean_ctor_get(x_411, 4);
lean_inc(x_504);
x_505 = lean_ctor_get(x_411, 5);
lean_inc(x_505);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 lean_ctor_release(x_411, 2);
 lean_ctor_release(x_411, 3);
 lean_ctor_release(x_411, 4);
 lean_ctor_release(x_411, 5);
 x_506 = x_411;
} else {
 lean_dec_ref(x_411);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(0, 6, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_500);
lean_ctor_set(x_507, 1, x_1);
lean_ctor_set(x_507, 2, x_502);
lean_ctor_set(x_507, 3, x_503);
lean_ctor_set(x_507, 4, x_504);
lean_ctor_set(x_507, 5, x_505);
lean_inc(x_4);
x_508 = l_Lean_Meta_SynthInstance_tryResolveCore(x_2, x_3, x_4, x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_ctor_get(x_509, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_509, 2);
lean_inc(x_512);
x_513 = lean_ctor_get(x_509, 3);
lean_inc(x_513);
x_514 = lean_ctor_get(x_509, 4);
lean_inc(x_514);
x_515 = lean_ctor_get(x_509, 5);
lean_inc(x_515);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 lean_ctor_release(x_509, 4);
 lean_ctor_release(x_509, 5);
 x_516 = x_509;
} else {
 lean_dec_ref(x_509);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(0, 6, 0);
} else {
 x_517 = x_516;
}
lean_ctor_set(x_517, 0, x_511);
lean_ctor_set(x_517, 1, x_501);
lean_ctor_set(x_517, 2, x_512);
lean_ctor_set(x_517, 3, x_513);
lean_ctor_set(x_517, 4, x_514);
lean_ctor_set(x_517, 5, x_515);
x_518 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_496);
lean_ctor_set(x_518, 2, x_497);
lean_ctor_set(x_518, 3, x_498);
lean_ctor_set(x_518, 4, x_499);
x_519 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_520 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_412, x_519, x_4, x_518);
lean_dec(x_4);
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_522 = x_520;
} else {
 lean_dec_ref(x_520);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(0, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_510);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_524 = lean_ctor_get(x_508, 1);
lean_inc(x_524);
x_525 = lean_ctor_get(x_508, 0);
lean_inc(x_525);
lean_dec(x_508);
x_526 = lean_ctor_get(x_524, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_524, 2);
lean_inc(x_527);
x_528 = lean_ctor_get(x_524, 3);
lean_inc(x_528);
x_529 = lean_ctor_get(x_524, 4);
lean_inc(x_529);
x_530 = lean_ctor_get(x_524, 5);
lean_inc(x_530);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 lean_ctor_release(x_524, 2);
 lean_ctor_release(x_524, 3);
 lean_ctor_release(x_524, 4);
 lean_ctor_release(x_524, 5);
 x_531 = x_524;
} else {
 lean_dec_ref(x_524);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(0, 6, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_526);
lean_ctor_set(x_532, 1, x_501);
lean_ctor_set(x_532, 2, x_527);
lean_ctor_set(x_532, 3, x_528);
lean_ctor_set(x_532, 4, x_529);
lean_ctor_set(x_532, 5, x_530);
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_496);
lean_ctor_set(x_533, 2, x_497);
lean_ctor_set(x_533, 3, x_498);
lean_ctor_set(x_533, 4, x_499);
x_534 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_535 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_412, x_534, x_4, x_533);
lean_dec(x_4);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_537 = x_535;
} else {
 lean_dec_ref(x_535);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_537;
 lean_ctor_set_tag(x_538, 1);
}
lean_ctor_set(x_538, 0, x_525);
lean_ctor_set(x_538, 1, x_536);
return x_538;
}
}
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_Trace_2__addNode___at_Lean_Meta_SynthInstance_tryResolve___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_SynthInstance_tryAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_41; lean_object* x_42; lean_object* x_70; 
x_11 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_6, 1, x_1);
lean_inc(x_4);
x_70 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_6);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Meta_isExprDefEq(x_2, x_74, x_4, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
lean_ctor_set(x_5, 0, x_78);
x_79 = lean_box(0);
x_12 = x_79;
x_13 = x_5;
goto block_40;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_dec(x_75);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_ctor_set(x_5, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_12 = x_82;
x_13 = x_5;
goto block_40;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec(x_75);
lean_ctor_set(x_5, 0, x_84);
x_41 = x_83;
x_42 = x_5;
goto block_69;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_4);
lean_dec(x_2);
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
lean_dec(x_70);
lean_ctor_set(x_5, 0, x_86);
x_41 = x_85;
x_42 = x_5;
goto block_69;
}
block_40:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_dec(x_17);
lean_ctor_set(x_15, 1, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 2);
x_21 = lean_ctor_get(x_15, 3);
x_22 = lean_ctor_get(x_15, 4);
x_23 = lean_ctor_get(x_15, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_13, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 2);
x_29 = lean_ctor_get(x_13, 3);
x_30 = lean_ctor_get(x_13, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 5);
lean_inc(x_35);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_36 = x_26;
} else {
 lean_dec_ref(x_26);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 6, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_11);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_34);
lean_ctor_set(x_37, 5, x_35);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_28);
lean_ctor_set(x_38, 3, x_29);
lean_ctor_set(x_38, 4, x_30);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
block_69:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 1);
lean_dec(x_46);
lean_ctor_set(x_44, 1, x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 2);
x_50 = lean_ctor_get(x_44, 3);
x_51 = lean_ctor_get(x_44, 4);
x_52 = lean_ctor_get(x_44, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_11);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set(x_53, 5, x_52);
lean_ctor_set(x_42, 0, x_53);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 1);
x_57 = lean_ctor_get(x_42, 2);
x_58 = lean_ctor_get(x_42, 3);
x_59 = lean_ctor_get(x_42, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 5);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 6, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_11);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_63);
lean_ctor_set(x_66, 5, x_64);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_57);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set(x_67, 4, x_59);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_41);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_111; lean_object* x_112; lean_object* x_129; lean_object* x_130; 
x_87 = lean_ctor_get(x_6, 0);
x_88 = lean_ctor_get(x_6, 1);
x_89 = lean_ctor_get(x_6, 2);
x_90 = lean_ctor_get(x_6, 3);
x_91 = lean_ctor_get(x_6, 4);
x_92 = lean_ctor_get(x_6, 5);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_6);
x_129 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_129, 0, x_87);
lean_ctor_set(x_129, 1, x_1);
lean_ctor_set(x_129, 2, x_89);
lean_ctor_set(x_129, 3, x_90);
lean_ctor_set(x_129, 4, x_91);
lean_ctor_set(x_129, 5, x_92);
lean_inc(x_4);
x_130 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Meta_isExprDefEq(x_2, x_134, x_4, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
lean_ctor_set(x_5, 0, x_138);
x_139 = lean_box(0);
x_93 = x_139;
x_94 = x_5;
goto block_110;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
lean_dec(x_135);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_ctor_set(x_5, 0, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_93 = x_142;
x_94 = x_5;
goto block_110;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 1);
lean_inc(x_144);
lean_dec(x_135);
lean_ctor_set(x_5, 0, x_144);
x_111 = x_143;
x_112 = x_5;
goto block_128;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_4);
lean_dec(x_2);
x_145 = lean_ctor_get(x_130, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_130, 1);
lean_inc(x_146);
lean_dec(x_130);
lean_ctor_set(x_5, 0, x_146);
x_111 = x_145;
x_112 = x_5;
goto block_128;
}
block_110:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_94, 4);
lean_inc(x_99);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 lean_ctor_release(x_94, 4);
 x_100 = x_94;
} else {
 lean_dec_ref(x_94);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_95, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_95, 4);
lean_inc(x_104);
x_105 = lean_ctor_get(x_95, 5);
lean_inc(x_105);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 lean_ctor_release(x_95, 2);
 lean_ctor_release(x_95, 3);
 lean_ctor_release(x_95, 4);
 lean_ctor_release(x_95, 5);
 x_106 = x_95;
} else {
 lean_dec_ref(x_95);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 6, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set(x_107, 1, x_88);
lean_ctor_set(x_107, 2, x_102);
lean_ctor_set(x_107, 3, x_103);
lean_ctor_set(x_107, 4, x_104);
lean_ctor_set(x_107, 5, x_105);
if (lean_is_scalar(x_100)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_100;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_96);
lean_ctor_set(x_108, 2, x_97);
lean_ctor_set(x_108, 3, x_98);
lean_ctor_set(x_108, 4, x_99);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
block_128:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 4);
lean_inc(x_117);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 x_118 = x_112;
} else {
 lean_dec_ref(x_112);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_113, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_113, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_113, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 lean_ctor_release(x_113, 5);
 x_124 = x_113;
} else {
 lean_dec_ref(x_113);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 6, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_88);
lean_ctor_set(x_125, 2, x_120);
lean_ctor_set(x_125, 3, x_121);
lean_ctor_set(x_125, 4, x_122);
lean_ctor_set(x_125, 5, x_123);
if (lean_is_scalar(x_118)) {
 x_126 = lean_alloc_ctor(0, 5, 0);
} else {
 x_126 = x_118;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_114);
lean_ctor_set(x_126, 2, x_115);
lean_ctor_set(x_126, 3, x_116);
lean_ctor_set(x_126, 4, x_117);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_111);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_176; lean_object* x_177; lean_object* x_194; lean_object* x_195; 
x_147 = lean_ctor_get(x_5, 1);
x_148 = lean_ctor_get(x_5, 2);
x_149 = lean_ctor_get(x_5, 3);
x_150 = lean_ctor_get(x_5, 4);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_5);
x_151 = lean_ctor_get(x_6, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_6, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_6, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_6, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_6, 4);
lean_inc(x_155);
x_156 = lean_ctor_get(x_6, 5);
lean_inc(x_156);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 x_157 = x_6;
} else {
 lean_dec_ref(x_6);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_194 = lean_alloc_ctor(0, 6, 0);
} else {
 x_194 = x_157;
}
lean_ctor_set(x_194, 0, x_151);
lean_ctor_set(x_194, 1, x_1);
lean_ctor_set(x_194, 2, x_153);
lean_ctor_set(x_194, 3, x_154);
lean_ctor_set(x_194, 4, x_155);
lean_ctor_set(x_194, 5, x_156);
lean_inc(x_4);
x_195 = l_Lean_Meta_openAbstractMVarsResult(x_7, x_4, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l_Lean_Meta_isExprDefEq(x_2, x_199, x_4, x_198);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_unbox(x_201);
lean_dec(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_147);
lean_ctor_set(x_204, 2, x_148);
lean_ctor_set(x_204, 3, x_149);
lean_ctor_set(x_204, 4, x_150);
x_205 = lean_box(0);
x_158 = x_205;
x_159 = x_204;
goto block_175;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_200, 1);
lean_inc(x_206);
lean_dec(x_200);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
x_208 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_147);
lean_ctor_set(x_208, 2, x_148);
lean_ctor_set(x_208, 3, x_149);
lean_ctor_set(x_208, 4, x_150);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_207);
x_158 = x_209;
x_159 = x_208;
goto block_175;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_200, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_200, 1);
lean_inc(x_211);
lean_dec(x_200);
x_212 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_147);
lean_ctor_set(x_212, 2, x_148);
lean_ctor_set(x_212, 3, x_149);
lean_ctor_set(x_212, 4, x_150);
x_176 = x_210;
x_177 = x_212;
goto block_193;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_4);
lean_dec(x_2);
x_213 = lean_ctor_get(x_195, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_195, 1);
lean_inc(x_214);
lean_dec(x_195);
x_215 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_147);
lean_ctor_set(x_215, 2, x_148);
lean_ctor_set(x_215, 3, x_149);
lean_ctor_set(x_215, 4, x_150);
x_176 = x_213;
x_177 = x_215;
goto block_193;
}
block_175:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 4);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 lean_ctor_release(x_159, 2);
 lean_ctor_release(x_159, 3);
 lean_ctor_release(x_159, 4);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_160, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_160, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_160, 5);
lean_inc(x_170);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 x_171 = x_160;
} else {
 lean_dec_ref(x_160);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 6, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_166);
lean_ctor_set(x_172, 1, x_152);
lean_ctor_set(x_172, 2, x_167);
lean_ctor_set(x_172, 3, x_168);
lean_ctor_set(x_172, 4, x_169);
lean_ctor_set(x_172, 5, x_170);
if (lean_is_scalar(x_165)) {
 x_173 = lean_alloc_ctor(0, 5, 0);
} else {
 x_173 = x_165;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_161);
lean_ctor_set(x_173, 2, x_162);
lean_ctor_set(x_173, 3, x_163);
lean_ctor_set(x_173, 4, x_164);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_158);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
block_193:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 4);
lean_inc(x_182);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 lean_ctor_release(x_177, 4);
 x_183 = x_177;
} else {
 lean_dec_ref(x_177);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_178, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_178, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_178, 5);
lean_inc(x_188);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 lean_ctor_release(x_178, 5);
 x_189 = x_178;
} else {
 lean_dec_ref(x_178);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 6, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_184);
lean_ctor_set(x_190, 1, x_152);
lean_ctor_set(x_190, 2, x_185);
lean_ctor_set(x_190, 3, x_186);
lean_ctor_set(x_190, 4, x_187);
lean_ctor_set(x_190, 5, x_188);
if (lean_is_scalar(x_183)) {
 x_191 = lean_alloc_ctor(0, 5, 0);
} else {
 x_191 = x_183;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_179);
lean_ctor_set(x_191, 2, x_180);
lean_ctor_set(x_191, 3, x_181);
lean_ctor_set(x_191, 4, x_182);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_176);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("skip answer containing metavariables ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_wakeUp___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_wakeUp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_wakeUp___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_wakeUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_array_push(x_7, x_8);
lean_ctor_set(x_4, 3, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_ctor_get(x_4, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
lean_inc(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_1);
x_19 = lean_array_push(x_16, x_18);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_110; uint8_t x_111; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_110 = lean_ctor_get(x_23, 0);
lean_inc(x_110);
x_111 = l_Array_isEmpty___rarg(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_box(0);
x_24 = x_112;
goto block_109;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_23, 1);
lean_inc(x_113);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_nat_dec_eq(x_113, x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
x_24 = x_116;
goto block_109;
}
else
{
uint8_t x_117; 
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_4);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_4, 1);
lean_dec(x_118);
x_119 = lean_ctor_get(x_23, 2);
lean_inc(x_119);
lean_dec(x_23);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_4, 1, x_120);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_123 = lean_ctor_get(x_4, 0);
x_124 = lean_ctor_get(x_4, 2);
x_125 = lean_ctor_get(x_4, 3);
x_126 = lean_ctor_get(x_4, 4);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_4);
x_127 = lean_ctor_get(x_23, 2);
lean_inc(x_127);
lean_dec(x_23);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_124);
lean_ctor_set(x_129, 3, x_125);
lean_ctor_set(x_129, 4, x_126);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
block_109:
{
uint8_t x_25; 
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_27 = l_Lean_Meta_openAbstractMVarsResult(x_23, x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_4, 0, x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_43 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_42, x_3, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_31);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_43, 0, x_48);
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_31);
x_54 = l_Lean_Meta_SynthInstance_wakeUp___closed__3;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_42, x_55, x_3, x_52);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_27);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_27, 1);
lean_ctor_set(x_4, 0, x_64);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_27, 0);
x_66 = lean_ctor_get(x_27, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_27);
lean_ctor_set(x_4, 0, x_66);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_4);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_4, 0);
x_69 = lean_ctor_get(x_4, 1);
x_70 = lean_ctor_get(x_4, 2);
x_71 = lean_ctor_get(x_4, 3);
x_72 = lean_ctor_get(x_4, 4);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_4);
lean_inc(x_3);
x_73 = l_Lean_Meta_openAbstractMVarsResult(x_23, x_3, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_70);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_72);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*1);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
lean_dec(x_3);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_88 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_87, x_3, x_86);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_78);
lean_dec(x_3);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_78);
x_97 = l_Lean_Meta_SynthInstance_wakeUp___closed__3;
x_98 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_87, x_98, x_3, x_95);
lean_dec(x_3);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_3);
x_104 = lean_ctor_get(x_73, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_73, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_106 = x_73;
} else {
 lean_dec_ref(x_73);
 x_106 = lean_box(0);
}
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_69);
lean_ctor_set(x_107, 2, x_70);
lean_ctor_set(x_107, 3, x_71);
lean_ctor_set(x_107, 4, x_72);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_wakeUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_wakeUp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_expr_eqv(x_9, x_10);
lean_dec(x_9);
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
uint8_t x_15; 
lean_dec(x_5);
x_15 = 1;
return x_15;
}
}
}
}
uint8_t l_Lean_Meta_SynthInstance_isNewAnswer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_SynthInstance_isNewAnswer___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_SynthInstance_isNewAnswer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SynthInstance_isNewAnswer(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_3, x_4);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_5);
x_15 = l_Lean_Meta_SynthInstance_wakeUp(x_7, x_12, x_5, x_6);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_4 = x_14;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("newAnswer");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_addAnswer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_addAnswer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_addAnswer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_40; uint8_t x_212; lean_object* x_213; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_10 = lean_ctor_get(x_4, 1);
lean_ctor_set(x_4, 1, x_5);
x_242 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_243, sizeof(void*)*1);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = 0;
x_212 = x_246;
x_213 = x_245;
goto block_241;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_247 = lean_ctor_get(x_242, 1);
lean_inc(x_247);
lean_dec(x_242);
x_248 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_249 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_248, x_2, x_247);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_unbox(x_250);
lean_dec(x_250);
x_212 = x_252;
x_213 = x_251;
goto block_241;
}
block_39:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_dec(x_16);
lean_ctor_set(x_14, 1, x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 2);
x_20 = lean_ctor_get(x_14, 3);
x_21 = lean_ctor_get(x_14, 4);
x_22 = lean_ctor_get(x_14, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_12, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_12, 2);
x_28 = lean_ctor_get(x_12, 3);
x_29 = lean_ctor_get(x_12, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 5);
lean_inc(x_34);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 x_35 = x_25;
} else {
 lean_dec_ref(x_25);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 6, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_10);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_34);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
block_211:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_abstractMVars(x_44, x_2, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
lean_inc(x_2);
x_50 = l_Lean_Meta_inferType(x_49, x_2, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_51);
lean_inc(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 1);
lean_dec(x_55);
lean_ctor_set(x_52, 1, x_10);
lean_ctor_set(x_40, 0, x_52);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
lean_dec(x_1);
lean_inc(x_2);
x_57 = l_Lean_Meta_SynthInstance_getEntry(x_56, x_2, x_40);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_57, 1);
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
x_64 = l_Lean_Meta_SynthInstance_isNewAnswer(x_63, x_53);
if (x_64 == 0)
{
lean_object* x_65; 
lean_free_object(x_59);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_65 = lean_box(0);
lean_ctor_set(x_57, 0, x_65);
return x_57;
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_free_object(x_57);
x_66 = lean_array_push(x_63, x_53);
lean_inc(x_62);
lean_ctor_set(x_59, 1, x_66);
x_67 = !lean_is_exclusive(x_61);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_61, 4);
x_69 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_68, x_56, x_59);
lean_ctor_set(x_61, 4, x_69);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_62, x_70, x_2, x_61);
lean_dec(x_62);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_72 = lean_ctor_get(x_61, 0);
x_73 = lean_ctor_get(x_61, 1);
x_74 = lean_ctor_get(x_61, 2);
x_75 = lean_ctor_get(x_61, 3);
x_76 = lean_ctor_get(x_61, 4);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_61);
x_77 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_76, x_56, x_59);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set(x_78, 3, x_75);
lean_ctor_set(x_78, 4, x_77);
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_62, x_79, x_2, x_78);
lean_dec(x_62);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_57, 1);
x_82 = lean_ctor_get(x_59, 0);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_59);
x_84 = l_Lean_Meta_SynthInstance_isNewAnswer(x_83, x_53);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_85 = lean_box(0);
lean_ctor_set(x_57, 0, x_85);
return x_57;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_57);
x_86 = lean_array_push(x_83, x_53);
lean_inc(x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 4);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
 x_93 = lean_box(0);
}
x_94 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_92, x_56, x_87);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 5, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_89);
lean_ctor_set(x_95, 2, x_90);
lean_ctor_set(x_95, 3, x_91);
lean_ctor_set(x_95, 4, x_94);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_82, x_96, x_2, x_95);
lean_dec(x_82);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_57, 0);
x_99 = lean_ctor_get(x_57, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_57);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
x_103 = l_Lean_Meta_SynthInstance_isNewAnswer(x_101, x_53);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_99);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_106 = lean_array_push(x_101, x_53);
lean_inc(x_100);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_102;
}
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_ctor_get(x_99, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_99, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_99, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_99, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_99, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 x_113 = x_99;
} else {
 lean_dec_ref(x_99);
 x_113 = lean_box(0);
}
x_114 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_112, x_56, x_107);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_111);
lean_ctor_set(x_115, 4, x_114);
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_100, x_116, x_2, x_115);
lean_dec(x_100);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_57);
if (x_118 == 0)
{
return x_57;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_57, 0);
x_120 = lean_ctor_get(x_57, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_57);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_52, 0);
x_123 = lean_ctor_get(x_52, 2);
x_124 = lean_ctor_get(x_52, 3);
x_125 = lean_ctor_get(x_52, 4);
x_126 = lean_ctor_get(x_52, 5);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_52);
x_127 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_10);
lean_ctor_set(x_127, 2, x_123);
lean_ctor_set(x_127, 3, x_124);
lean_ctor_set(x_127, 4, x_125);
lean_ctor_set(x_127, 5, x_126);
lean_ctor_set(x_40, 0, x_127);
x_128 = lean_ctor_get(x_1, 1);
lean_inc(x_128);
lean_dec(x_1);
lean_inc(x_2);
x_129 = l_Lean_Meta_SynthInstance_getEntry(x_128, x_2, x_40);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = l_Lean_Meta_SynthInstance_isNewAnswer(x_134, x_53);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_128);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_137 = lean_box(0);
if (lean_is_scalar(x_132)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_132;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_131);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_132);
x_139 = lean_array_push(x_134, x_53);
lean_inc(x_133);
if (lean_is_scalar(x_135)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_135;
}
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_ctor_get(x_131, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_131, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_131, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_131, 4);
lean_inc(x_145);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 x_146 = x_131;
} else {
 lean_dec_ref(x_131);
 x_146 = lean_box(0);
}
x_147 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_145, x_128, x_140);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_142);
lean_ctor_set(x_148, 2, x_143);
lean_ctor_set(x_148, 3, x_144);
lean_ctor_set(x_148, 4, x_147);
x_149 = lean_unsigned_to_nat(0u);
x_150 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_47, x_51, x_133, x_149, x_2, x_148);
lean_dec(x_133);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_128);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_2);
x_151 = lean_ctor_get(x_129, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_129, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_153 = x_129;
} else {
 lean_dec_ref(x_129);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_47);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_ctor_get(x_50, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_50, 1);
lean_inc(x_156);
lean_dec(x_50);
lean_ctor_set(x_40, 0, x_156);
x_11 = x_155;
x_12 = x_40;
goto block_39;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_157 = lean_ctor_get(x_40, 0);
x_158 = lean_ctor_get(x_40, 1);
x_159 = lean_ctor_get(x_40, 2);
x_160 = lean_ctor_get(x_40, 3);
x_161 = lean_ctor_get(x_40, 4);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_40);
x_162 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_157);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Meta_abstractMVars(x_163, x_2, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 2);
lean_inc(x_168);
lean_inc(x_2);
x_169 = l_Lean_Meta_inferType(x_168, x_2, x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_170);
lean_inc(x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_166);
lean_ctor_set(x_172, 1, x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_171, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_171, 5);
lean_inc(x_177);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 lean_ctor_release(x_171, 4);
 lean_ctor_release(x_171, 5);
 x_178 = x_171;
} else {
 lean_dec_ref(x_171);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 6, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set(x_179, 1, x_10);
lean_ctor_set(x_179, 2, x_174);
lean_ctor_set(x_179, 3, x_175);
lean_ctor_set(x_179, 4, x_176);
lean_ctor_set(x_179, 5, x_177);
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_158);
lean_ctor_set(x_180, 2, x_159);
lean_ctor_set(x_180, 3, x_160);
lean_ctor_set(x_180, 4, x_161);
x_181 = lean_ctor_get(x_1, 1);
lean_inc(x_181);
lean_dec(x_1);
lean_inc(x_2);
x_182 = l_Lean_Meta_SynthInstance_getEntry(x_181, x_2, x_180);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_188 = x_183;
} else {
 lean_dec_ref(x_183);
 x_188 = lean_box(0);
}
x_189 = l_Lean_Meta_SynthInstance_isNewAnswer(x_187, x_172);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_181);
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_2);
x_190 = lean_box(0);
if (lean_is_scalar(x_185)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_185;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_184);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_185);
x_192 = lean_array_push(x_187, x_172);
lean_inc(x_186);
if (lean_is_scalar(x_188)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_188;
}
lean_ctor_set(x_193, 0, x_186);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_ctor_get(x_184, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_184, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_184, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_184, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_184, 4);
lean_inc(x_198);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 x_199 = x_184;
} else {
 lean_dec_ref(x_184);
 x_199 = lean_box(0);
}
x_200 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_198, x_181, x_193);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 5, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_195);
lean_ctor_set(x_201, 2, x_196);
lean_ctor_set(x_201, 3, x_197);
lean_ctor_set(x_201, 4, x_200);
x_202 = lean_unsigned_to_nat(0u);
x_203 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_166, x_170, x_186, x_202, x_2, x_201);
lean_dec(x_186);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_181);
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_2);
x_204 = lean_ctor_get(x_182, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_182, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_206 = x_182;
} else {
 lean_dec_ref(x_182);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_166);
lean_dec(x_2);
lean_dec(x_1);
x_208 = lean_ctor_get(x_169, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_169, 1);
lean_inc(x_209);
lean_dec(x_169);
x_210 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_158);
lean_ctor_set(x_210, 2, x_159);
lean_ctor_set(x_210, 3, x_160);
lean_ctor_set(x_210, 4, x_161);
x_11 = x_208;
x_12 = x_210;
goto block_39;
}
}
}
block_241:
{
if (x_212 == 0)
{
x_40 = x_213;
goto block_211;
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_2);
lean_inc(x_6);
x_216 = l_Lean_Meta_inferType(x_6, x_2, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
lean_ctor_set(x_213, 0, x_218);
x_219 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_219, 0, x_217);
x_220 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_221 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_220, x_219, x_2, x_213);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_40 = x_222;
goto block_211;
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_216, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_216, 1);
lean_inc(x_224);
lean_dec(x_216);
lean_ctor_set(x_213, 0, x_224);
x_11 = x_223;
x_12 = x_213;
goto block_39;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_213, 0);
x_226 = lean_ctor_get(x_213, 1);
x_227 = lean_ctor_get(x_213, 2);
x_228 = lean_ctor_get(x_213, 3);
x_229 = lean_ctor_get(x_213, 4);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_213);
lean_inc(x_2);
lean_inc(x_6);
x_230 = l_Lean_Meta_inferType(x_6, x_2, x_225);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_226);
lean_ctor_set(x_233, 2, x_227);
lean_ctor_set(x_233, 3, x_228);
lean_ctor_set(x_233, 4, x_229);
x_234 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_234, 0, x_231);
x_235 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_236 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_235, x_234, x_2, x_233);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_40 = x_237;
goto block_211;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_230, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_230, 1);
lean_inc(x_239);
lean_dec(x_230);
x_240 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_226);
lean_ctor_set(x_240, 2, x_227);
lean_ctor_set(x_240, 3, x_228);
lean_ctor_set(x_240, 4, x_229);
x_11 = x_238;
x_12 = x_240;
goto block_39;
}
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_277; uint8_t x_334; lean_object* x_335; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_253 = lean_ctor_get(x_4, 0);
x_254 = lean_ctor_get(x_4, 1);
x_255 = lean_ctor_get(x_4, 2);
x_256 = lean_ctor_get(x_4, 3);
x_257 = lean_ctor_get(x_4, 4);
x_258 = lean_ctor_get(x_4, 5);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_4);
x_354 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_354, 0, x_253);
lean_ctor_set(x_354, 1, x_5);
lean_ctor_set(x_354, 2, x_255);
lean_ctor_set(x_354, 3, x_256);
lean_ctor_set(x_354, 4, x_257);
lean_ctor_set(x_354, 5, x_258);
lean_ctor_set(x_3, 0, x_354);
x_355 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get_uint8(x_356, sizeof(void*)*1);
lean_dec(x_356);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
lean_dec(x_355);
x_359 = 0;
x_334 = x_359;
x_335 = x_358;
goto block_353;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_360 = lean_ctor_get(x_355, 1);
lean_inc(x_360);
lean_dec(x_355);
x_361 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_362 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_361, x_2, x_360);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = lean_unbox(x_363);
lean_dec(x_363);
x_334 = x_365;
x_335 = x_364;
goto block_353;
}
block_276:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_260, 2);
lean_inc(x_263);
x_264 = lean_ctor_get(x_260, 3);
lean_inc(x_264);
x_265 = lean_ctor_get(x_260, 4);
lean_inc(x_265);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 lean_ctor_release(x_260, 4);
 x_266 = x_260;
} else {
 lean_dec_ref(x_260);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_261, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_261, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_261, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_261, 4);
lean_inc(x_270);
x_271 = lean_ctor_get(x_261, 5);
lean_inc(x_271);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 lean_ctor_release(x_261, 5);
 x_272 = x_261;
} else {
 lean_dec_ref(x_261);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(0, 6, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_267);
lean_ctor_set(x_273, 1, x_254);
lean_ctor_set(x_273, 2, x_268);
lean_ctor_set(x_273, 3, x_269);
lean_ctor_set(x_273, 4, x_270);
lean_ctor_set(x_273, 5, x_271);
if (lean_is_scalar(x_266)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_266;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_262);
lean_ctor_set(x_274, 2, x_263);
lean_ctor_set(x_274, 3, x_264);
lean_ctor_set(x_274, 4, x_265);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_259);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
block_333:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_277, 3);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 4);
lean_inc(x_282);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 lean_ctor_release(x_277, 3);
 lean_ctor_release(x_277, 4);
 x_283 = x_277;
} else {
 lean_dec_ref(x_277);
 x_283 = lean_box(0);
}
x_284 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_278);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = l_Lean_Meta_abstractMVars(x_285, x_2, x_286);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_ctor_get(x_288, 2);
lean_inc(x_290);
lean_inc(x_2);
x_291 = l_Lean_Meta_inferType(x_290, x_2, x_289);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
lean_inc(x_292);
lean_inc(x_288);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_292);
x_295 = lean_ctor_get(x_293, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_293, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_293, 3);
lean_inc(x_297);
x_298 = lean_ctor_get(x_293, 4);
lean_inc(x_298);
x_299 = lean_ctor_get(x_293, 5);
lean_inc(x_299);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 lean_ctor_release(x_293, 2);
 lean_ctor_release(x_293, 3);
 lean_ctor_release(x_293, 4);
 lean_ctor_release(x_293, 5);
 x_300 = x_293;
} else {
 lean_dec_ref(x_293);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(0, 6, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_295);
lean_ctor_set(x_301, 1, x_254);
lean_ctor_set(x_301, 2, x_296);
lean_ctor_set(x_301, 3, x_297);
lean_ctor_set(x_301, 4, x_298);
lean_ctor_set(x_301, 5, x_299);
if (lean_is_scalar(x_283)) {
 x_302 = lean_alloc_ctor(0, 5, 0);
} else {
 x_302 = x_283;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_279);
lean_ctor_set(x_302, 2, x_280);
lean_ctor_set(x_302, 3, x_281);
lean_ctor_set(x_302, 4, x_282);
x_303 = lean_ctor_get(x_1, 1);
lean_inc(x_303);
lean_dec(x_1);
lean_inc(x_2);
x_304 = l_Lean_Meta_SynthInstance_getEntry(x_303, x_2, x_302);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_307 = x_304;
} else {
 lean_dec_ref(x_304);
 x_307 = lean_box(0);
}
x_308 = lean_ctor_get(x_305, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_310 = x_305;
} else {
 lean_dec_ref(x_305);
 x_310 = lean_box(0);
}
x_311 = l_Lean_Meta_SynthInstance_isNewAnswer(x_309, x_294);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_303);
lean_dec(x_294);
lean_dec(x_292);
lean_dec(x_288);
lean_dec(x_2);
x_312 = lean_box(0);
if (lean_is_scalar(x_307)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_307;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_306);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_307);
x_314 = lean_array_push(x_309, x_294);
lean_inc(x_308);
if (lean_is_scalar(x_310)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_310;
}
lean_ctor_set(x_315, 0, x_308);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_ctor_get(x_306, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_306, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_306, 2);
lean_inc(x_318);
x_319 = lean_ctor_get(x_306, 3);
lean_inc(x_319);
x_320 = lean_ctor_get(x_306, 4);
lean_inc(x_320);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 lean_ctor_release(x_306, 4);
 x_321 = x_306;
} else {
 lean_dec_ref(x_306);
 x_321 = lean_box(0);
}
x_322 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_320, x_303, x_315);
if (lean_is_scalar(x_321)) {
 x_323 = lean_alloc_ctor(0, 5, 0);
} else {
 x_323 = x_321;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set(x_323, 4, x_322);
x_324 = lean_unsigned_to_nat(0u);
x_325 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_288, x_292, x_308, x_324, x_2, x_323);
lean_dec(x_308);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_303);
lean_dec(x_294);
lean_dec(x_292);
lean_dec(x_288);
lean_dec(x_2);
x_326 = lean_ctor_get(x_304, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_304, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_328 = x_304;
} else {
 lean_dec_ref(x_304);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_288);
lean_dec(x_2);
lean_dec(x_1);
x_330 = lean_ctor_get(x_291, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_291, 1);
lean_inc(x_331);
lean_dec(x_291);
if (lean_is_scalar(x_283)) {
 x_332 = lean_alloc_ctor(0, 5, 0);
} else {
 x_332 = x_283;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_279);
lean_ctor_set(x_332, 2, x_280);
lean_ctor_set(x_332, 3, x_281);
lean_ctor_set(x_332, 4, x_282);
x_259 = x_330;
x_260 = x_332;
goto block_276;
}
}
block_353:
{
if (x_334 == 0)
{
x_277 = x_335;
goto block_333;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_335, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_335, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_335, 4);
lean_inc(x_340);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 lean_ctor_release(x_335, 2);
 lean_ctor_release(x_335, 3);
 lean_ctor_release(x_335, 4);
 x_341 = x_335;
} else {
 lean_dec_ref(x_335);
 x_341 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_6);
x_342 = l_Lean_Meta_inferType(x_6, x_2, x_336);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
if (lean_is_scalar(x_341)) {
 x_345 = lean_alloc_ctor(0, 5, 0);
} else {
 x_345 = x_341;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_337);
lean_ctor_set(x_345, 2, x_338);
lean_ctor_set(x_345, 3, x_339);
lean_ctor_set(x_345, 4, x_340);
x_346 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_346, 0, x_343);
x_347 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_348 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_347, x_346, x_2, x_345);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
x_277 = x_349;
goto block_333;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_350 = lean_ctor_get(x_342, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_342, 1);
lean_inc(x_351);
lean_dec(x_342);
if (lean_is_scalar(x_341)) {
 x_352 = lean_alloc_ctor(0, 5, 0);
} else {
 x_352 = x_341;
}
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_337);
lean_ctor_set(x_352, 2, x_338);
lean_ctor_set(x_352, 3, x_339);
lean_ctor_set(x_352, 4, x_340);
x_259 = x_350;
x_260 = x_352;
goto block_276;
}
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_395; uint8_t x_452; lean_object* x_453; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_366 = lean_ctor_get(x_3, 1);
x_367 = lean_ctor_get(x_3, 2);
x_368 = lean_ctor_get(x_3, 3);
x_369 = lean_ctor_get(x_3, 4);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_3);
x_370 = lean_ctor_get(x_4, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_4, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_4, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_4, 3);
lean_inc(x_373);
x_374 = lean_ctor_get(x_4, 4);
lean_inc(x_374);
x_375 = lean_ctor_get(x_4, 5);
lean_inc(x_375);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_376 = x_4;
} else {
 lean_dec_ref(x_4);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_472 = lean_alloc_ctor(0, 6, 0);
} else {
 x_472 = x_376;
}
lean_ctor_set(x_472, 0, x_370);
lean_ctor_set(x_472, 1, x_5);
lean_ctor_set(x_472, 2, x_372);
lean_ctor_set(x_472, 3, x_373);
lean_ctor_set(x_472, 4, x_374);
lean_ctor_set(x_472, 5, x_375);
x_473 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_366);
lean_ctor_set(x_473, 2, x_367);
lean_ctor_set(x_473, 3, x_368);
lean_ctor_set(x_473, 4, x_369);
x_474 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_473);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get_uint8(x_475, sizeof(void*)*1);
lean_dec(x_475);
if (x_476 == 0)
{
lean_object* x_477; uint8_t x_478; 
x_477 = lean_ctor_get(x_474, 1);
lean_inc(x_477);
lean_dec(x_474);
x_478 = 0;
x_452 = x_478;
x_453 = x_477;
goto block_471;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_479 = lean_ctor_get(x_474, 1);
lean_inc(x_479);
lean_dec(x_474);
x_480 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_481 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_480, x_2, x_479);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_unbox(x_482);
lean_dec(x_482);
x_452 = x_484;
x_453 = x_483;
goto block_471;
}
block_394:
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_378, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_378, 3);
lean_inc(x_382);
x_383 = lean_ctor_get(x_378, 4);
lean_inc(x_383);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 lean_ctor_release(x_378, 4);
 x_384 = x_378;
} else {
 lean_dec_ref(x_378);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_379, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_379, 2);
lean_inc(x_386);
x_387 = lean_ctor_get(x_379, 3);
lean_inc(x_387);
x_388 = lean_ctor_get(x_379, 4);
lean_inc(x_388);
x_389 = lean_ctor_get(x_379, 5);
lean_inc(x_389);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 lean_ctor_release(x_379, 4);
 lean_ctor_release(x_379, 5);
 x_390 = x_379;
} else {
 lean_dec_ref(x_379);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(0, 6, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_385);
lean_ctor_set(x_391, 1, x_371);
lean_ctor_set(x_391, 2, x_386);
lean_ctor_set(x_391, 3, x_387);
lean_ctor_set(x_391, 4, x_388);
lean_ctor_set(x_391, 5, x_389);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(0, 5, 0);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_380);
lean_ctor_set(x_392, 2, x_381);
lean_ctor_set(x_392, 3, x_382);
lean_ctor_set(x_392, 4, x_383);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_377);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
block_451:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_395, 2);
lean_inc(x_398);
x_399 = lean_ctor_get(x_395, 3);
lean_inc(x_399);
x_400 = lean_ctor_get(x_395, 4);
lean_inc(x_400);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 lean_ctor_release(x_395, 2);
 lean_ctor_release(x_395, 3);
 lean_ctor_release(x_395, 4);
 x_401 = x_395;
} else {
 lean_dec_ref(x_395);
 x_401 = lean_box(0);
}
x_402 = l_Lean_Meta_instantiateMVars(x_6, x_2, x_396);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = l_Lean_Meta_abstractMVars(x_403, x_2, x_404);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_ctor_get(x_406, 2);
lean_inc(x_408);
lean_inc(x_2);
x_409 = l_Lean_Meta_inferType(x_408, x_2, x_407);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
lean_inc(x_410);
lean_inc(x_406);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_406);
lean_ctor_set(x_412, 1, x_410);
x_413 = lean_ctor_get(x_411, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_411, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_411, 3);
lean_inc(x_415);
x_416 = lean_ctor_get(x_411, 4);
lean_inc(x_416);
x_417 = lean_ctor_get(x_411, 5);
lean_inc(x_417);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 lean_ctor_release(x_411, 2);
 lean_ctor_release(x_411, 3);
 lean_ctor_release(x_411, 4);
 lean_ctor_release(x_411, 5);
 x_418 = x_411;
} else {
 lean_dec_ref(x_411);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 6, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_413);
lean_ctor_set(x_419, 1, x_371);
lean_ctor_set(x_419, 2, x_414);
lean_ctor_set(x_419, 3, x_415);
lean_ctor_set(x_419, 4, x_416);
lean_ctor_set(x_419, 5, x_417);
if (lean_is_scalar(x_401)) {
 x_420 = lean_alloc_ctor(0, 5, 0);
} else {
 x_420 = x_401;
}
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_397);
lean_ctor_set(x_420, 2, x_398);
lean_ctor_set(x_420, 3, x_399);
lean_ctor_set(x_420, 4, x_400);
x_421 = lean_ctor_get(x_1, 1);
lean_inc(x_421);
lean_dec(x_1);
lean_inc(x_2);
x_422 = l_Lean_Meta_SynthInstance_getEntry(x_421, x_2, x_420);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_425 = x_422;
} else {
 lean_dec_ref(x_422);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_423, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_423, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_428 = x_423;
} else {
 lean_dec_ref(x_423);
 x_428 = lean_box(0);
}
x_429 = l_Lean_Meta_SynthInstance_isNewAnswer(x_427, x_412);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_421);
lean_dec(x_412);
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_2);
x_430 = lean_box(0);
if (lean_is_scalar(x_425)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_425;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_424);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_425);
x_432 = lean_array_push(x_427, x_412);
lean_inc(x_426);
if (lean_is_scalar(x_428)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_428;
}
lean_ctor_set(x_433, 0, x_426);
lean_ctor_set(x_433, 1, x_432);
x_434 = lean_ctor_get(x_424, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_424, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_424, 4);
lean_inc(x_438);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 lean_ctor_release(x_424, 4);
 x_439 = x_424;
} else {
 lean_dec_ref(x_424);
 x_439 = lean_box(0);
}
x_440 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_438, x_421, x_433);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(0, 5, 0);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_434);
lean_ctor_set(x_441, 1, x_435);
lean_ctor_set(x_441, 2, x_436);
lean_ctor_set(x_441, 3, x_437);
lean_ctor_set(x_441, 4, x_440);
x_442 = lean_unsigned_to_nat(0u);
x_443 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_406, x_410, x_426, x_442, x_2, x_441);
lean_dec(x_426);
return x_443;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_421);
lean_dec(x_412);
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_2);
x_444 = lean_ctor_get(x_422, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_422, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_446 = x_422;
} else {
 lean_dec_ref(x_422);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_445);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_406);
lean_dec(x_2);
lean_dec(x_1);
x_448 = lean_ctor_get(x_409, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_409, 1);
lean_inc(x_449);
lean_dec(x_409);
if (lean_is_scalar(x_401)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_401;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_397);
lean_ctor_set(x_450, 2, x_398);
lean_ctor_set(x_450, 3, x_399);
lean_ctor_set(x_450, 4, x_400);
x_377 = x_448;
x_378 = x_450;
goto block_394;
}
}
block_471:
{
if (x_452 == 0)
{
x_395 = x_453;
goto block_451;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
x_456 = lean_ctor_get(x_453, 2);
lean_inc(x_456);
x_457 = lean_ctor_get(x_453, 3);
lean_inc(x_457);
x_458 = lean_ctor_get(x_453, 4);
lean_inc(x_458);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 lean_ctor_release(x_453, 2);
 lean_ctor_release(x_453, 3);
 lean_ctor_release(x_453, 4);
 x_459 = x_453;
} else {
 lean_dec_ref(x_453);
 x_459 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_6);
x_460 = l_Lean_Meta_inferType(x_6, x_2, x_454);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
if (lean_is_scalar(x_459)) {
 x_463 = lean_alloc_ctor(0, 5, 0);
} else {
 x_463 = x_459;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_455);
lean_ctor_set(x_463, 2, x_456);
lean_ctor_set(x_463, 3, x_457);
lean_ctor_set(x_463, 4, x_458);
x_464 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_464, 0, x_461);
x_465 = l_Lean_Meta_SynthInstance_addAnswer___closed__2;
x_466 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_465, x_464, x_2, x_463);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_395 = x_467;
goto block_451;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_468 = lean_ctor_get(x_460, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_460, 1);
lean_inc(x_469);
lean_dec(x_460);
if (lean_is_scalar(x_459)) {
 x_470 = lean_alloc_ctor(0, 5, 0);
} else {
 x_470 = x_459;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_455);
lean_ctor_set(x_470, 2, x_456);
lean_ctor_set(x_470, 3, x_457);
lean_ctor_set(x_470, 4, x_458);
x_377 = x_468;
x_378 = x_470;
goto block_394;
}
}
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forMAux___main___at_Lean_Meta_SynthInstance_addAnswer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_array_push(x_5, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_consume(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_addAnswer(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_8);
x_9 = l_Lean_Meta_SynthInstance_mkTableKeyFor(x_8, x_6, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_SynthInstance_findEntry_x3f(x_10, x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_SynthInstance_newSubgoal(x_8, x_10, x_6, x_7, x_2, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_17, 3);
x_22 = lean_ctor_get(x_17, 4);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_19, x_24, x_25, x_21);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_19, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_array_push(x_23, x_7);
lean_ctor_set(x_19, 0, x_30);
x_31 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_22, x_10, x_19);
lean_ctor_set(x_17, 4, x_31);
lean_ctor_set(x_17, 3, x_26);
x_32 = lean_box(0);
lean_ctor_set(x_12, 0, x_32);
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
x_33 = lean_array_push(x_23, x_7);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
x_35 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_22, x_10, x_34);
lean_ctor_set(x_17, 4, x_35);
lean_ctor_set(x_17, 3, x_26);
x_36 = lean_box(0);
lean_ctor_set(x_12, 0, x_36);
return x_12;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
x_39 = lean_ctor_get(x_17, 2);
x_40 = lean_ctor_get(x_17, 3);
x_41 = lean_ctor_get(x_17, 4);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_19, x_43, x_44, x_40);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_46 = x_19;
} else {
 lean_dec_ref(x_19);
 x_46 = lean_box(0);
}
x_47 = lean_array_push(x_42, x_7);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
x_49 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_41, x_10, x_48);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_38);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_box(0);
lean_ctor_set(x_12, 1, x_50);
lean_ctor_set(x_12, 0, x_51);
return x_12;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
lean_dec(x_13);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 4);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_53, x_61, x_62, x_57);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_64 = x_53;
} else {
 lean_dec_ref(x_53);
 x_64 = lean_box(0);
}
x_65 = lean_array_push(x_60, x_7);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
x_67 = l_HashMapImp_insert___at_Lean_Meta_SynthInstance_newSubgoal___spec__1(x_58, x_10, x_66);
if (lean_is_scalar(x_59)) {
 x_68 = lean_alloc_ctor(0, 5, 0);
} else {
 x_68 = x_59;
}
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_55);
lean_ctor_set(x_68, 2, x_56);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_9);
if (x_71 == 0)
{
return x_9;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_9, 0);
x_73 = lean_ctor_get(x_9, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_9);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_SynthInstance_consume___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTop___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(x_2);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getTop___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Meta_SynthInstance_getTop___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getTop___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getTop(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_modifyTop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
x_9 = lean_nat_dec_lt(x_8, x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_array_fget(x_5, x_8);
x_13 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_14 = lean_array_fset(x_5, x_8, x_13);
x_15 = lean_apply_1(x_1, x_12);
x_16 = lean_array_fset(x_14, x_8, x_15);
lean_dec(x_8);
lean_ctor_set(x_3, 2, x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
x_23 = lean_ctor_get(x_3, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_24 = lean_array_get_size(x_21);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
x_27 = lean_nat_dec_lt(x_26, x_24);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 4, x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_array_fget(x_21, x_26);
x_32 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_33 = lean_array_fset(x_21, x_26, x_32);
x_34 = lean_apply_1(x_1, x_31);
x_35 = lean_array_fset(x_33, x_26, x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_20);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_22);
lean_ctor_set(x_36, 4, x_23);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_modifyTop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_modifyTop(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("generate");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_generate___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instance ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_generate___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_generate___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_generate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_SynthInstance_getTop___rarg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_free_object(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = l_Lean_Expr_Inhabited;
x_17 = lean_array_get(x_16, x_10, x_15);
lean_dec(x_10);
x_141 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_6);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_18 = x_144;
goto block_140;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_147 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_146, x_1, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_18 = x_150;
goto block_140;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
lean_inc(x_17);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_17);
x_153 = l_Lean_Meta_SynthInstance_generate___closed__5;
x_154 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_146, x_154, x_1, x_151);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_18 = x_156;
goto block_140;
}
}
block_140:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 2);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_sub(x_21, x_14);
x_23 = lean_nat_dec_lt(x_22, x_21);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_15);
lean_inc(x_1);
lean_inc(x_7);
x_24 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_8);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = l_Lean_Meta_SynthInstance_consume(x_36, x_1, x_33);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_array_fget(x_20, x_22);
x_43 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_44 = lean_array_fset(x_20, x_22, x_43);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 4);
lean_dec(x_46);
lean_ctor_set(x_42, 4, x_15);
x_47 = lean_array_fset(x_44, x_22, x_42);
lean_dec(x_22);
lean_ctor_set(x_18, 2, x_47);
lean_inc(x_1);
lean_inc(x_7);
x_48 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_18);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_dec(x_48);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_7);
lean_ctor_set(x_60, 1, x_8);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
x_61 = l_Lean_Meta_SynthInstance_consume(x_60, x_1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
return x_48;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_42, 0);
x_67 = lean_ctor_get(x_42, 1);
x_68 = lean_ctor_get(x_42, 2);
x_69 = lean_ctor_get(x_42, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_42);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set(x_70, 4, x_15);
x_71 = lean_array_fset(x_44, x_22, x_70);
lean_dec(x_22);
lean_ctor_set(x_18, 2, x_71);
lean_inc(x_1);
lean_inc(x_7);
x_72 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_18);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_7);
lean_ctor_set(x_82, 1, x_8);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_81);
x_83 = l_Lean_Meta_SynthInstance_consume(x_82, x_1, x_79);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_84 = lean_ctor_get(x_72, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_72, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_86 = x_72;
} else {
 lean_dec_ref(x_72);
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
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_18, 0);
x_89 = lean_ctor_get(x_18, 1);
x_90 = lean_ctor_get(x_18, 2);
x_91 = lean_ctor_get(x_18, 3);
x_92 = lean_ctor_get(x_18, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_18);
x_93 = lean_array_get_size(x_90);
x_94 = lean_nat_sub(x_93, x_14);
x_95 = lean_nat_dec_lt(x_94, x_93);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_94);
lean_dec(x_15);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_89);
lean_ctor_set(x_96, 2, x_90);
lean_ctor_set(x_96, 3, x_91);
lean_ctor_set(x_96, 4, x_92);
lean_inc(x_1);
lean_inc(x_7);
x_97 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_dec(x_97);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_7);
lean_ctor_set(x_107, 1, x_8);
lean_ctor_set(x_107, 2, x_105);
lean_ctor_set(x_107, 3, x_106);
x_108 = l_Lean_Meta_SynthInstance_consume(x_107, x_1, x_104);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_109 = lean_ctor_get(x_97, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_111 = x_97;
} else {
 lean_dec_ref(x_97);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_array_fget(x_90, x_94);
x_114 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_115 = lean_array_fset(x_90, x_94, x_114);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 3);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 5, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_117);
lean_ctor_set(x_121, 2, x_118);
lean_ctor_set(x_121, 3, x_119);
lean_ctor_set(x_121, 4, x_15);
x_122 = lean_array_fset(x_115, x_94, x_121);
lean_dec(x_94);
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_88);
lean_ctor_set(x_123, 1, x_89);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_91);
lean_ctor_set(x_123, 4, x_92);
lean_inc(x_1);
lean_inc(x_7);
x_124 = l_Lean_Meta_SynthInstance_tryResolve(x_9, x_7, x_17, x_1, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_7);
lean_ctor_set(x_134, 1, x_8);
lean_ctor_set(x_134, 2, x_132);
lean_ctor_set(x_134, 3, x_133);
x_135 = l_Lean_Meta_SynthInstance_consume(x_134, x_1, x_131);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_136 = lean_ctor_get(x_124, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_124, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_138 = x_124;
} else {
 lean_dec_ref(x_124);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_6);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_6, 2);
x_159 = lean_array_pop(x_158);
lean_ctor_set(x_6, 2, x_159);
x_160 = lean_box(0);
lean_ctor_set(x_3, 0, x_160);
return x_3;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_161 = lean_ctor_get(x_6, 0);
x_162 = lean_ctor_get(x_6, 1);
x_163 = lean_ctor_get(x_6, 2);
x_164 = lean_ctor_get(x_6, 3);
x_165 = lean_ctor_get(x_6, 4);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_6);
x_166 = lean_array_pop(x_163);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_166);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set(x_167, 4, x_165);
x_168 = lean_box(0);
lean_ctor_set(x_3, 1, x_167);
lean_ctor_set(x_3, 0, x_168);
return x_3;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_169 = lean_ctor_get(x_3, 0);
x_170 = lean_ctor_get(x_3, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_3);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 4);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_nat_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_nat_sub(x_175, x_178);
lean_dec(x_175);
x_180 = l_Lean_Expr_Inhabited;
x_181 = lean_array_get(x_180, x_174, x_179);
lean_dec(x_174);
x_237 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_170);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_238, sizeof(void*)*1);
lean_dec(x_238);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_182 = x_240;
goto block_236;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
lean_dec(x_237);
x_242 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_243 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_242, x_1, x_241);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_182 = x_246;
goto block_236;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
lean_dec(x_243);
lean_inc(x_181);
x_248 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_248, 0, x_181);
x_249 = l_Lean_Meta_SynthInstance_generate___closed__5;
x_250 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_242, x_250, x_1, x_247);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_182 = x_252;
goto block_236;
}
}
block_236:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_182, 4);
lean_inc(x_187);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 x_188 = x_182;
} else {
 lean_dec_ref(x_182);
 x_188 = lean_box(0);
}
x_189 = lean_array_get_size(x_185);
x_190 = lean_nat_sub(x_189, x_178);
x_191 = lean_nat_dec_lt(x_190, x_189);
lean_dec(x_189);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_190);
lean_dec(x_179);
if (lean_is_scalar(x_188)) {
 x_192 = lean_alloc_ctor(0, 5, 0);
} else {
 x_192 = x_188;
}
lean_ctor_set(x_192, 0, x_183);
lean_ctor_set(x_192, 1, x_184);
lean_ctor_set(x_192, 2, x_185);
lean_ctor_set(x_192, 3, x_186);
lean_ctor_set(x_192, 4, x_187);
lean_inc(x_1);
lean_inc(x_171);
x_193 = l_Lean_Meta_SynthInstance_tryResolve(x_173, x_171, x_181, x_1, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
x_197 = lean_box(0);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_195);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
lean_dec(x_194);
x_200 = lean_ctor_get(x_193, 1);
lean_inc(x_200);
lean_dec(x_193);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_dec(x_199);
x_203 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_203, 0, x_171);
lean_ctor_set(x_203, 1, x_172);
lean_ctor_set(x_203, 2, x_201);
lean_ctor_set(x_203, 3, x_202);
x_204 = l_Lean_Meta_SynthInstance_consume(x_203, x_1, x_200);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_205 = lean_ctor_get(x_193, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_193, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_207 = x_193;
} else {
 lean_dec_ref(x_193);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_209 = lean_array_fget(x_185, x_190);
x_210 = l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1;
x_211 = lean_array_fset(x_185, x_190, x_210);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_209, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_209, 3);
lean_inc(x_215);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 lean_ctor_release(x_209, 4);
 x_216 = x_209;
} else {
 lean_dec_ref(x_209);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 5, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_212);
lean_ctor_set(x_217, 1, x_213);
lean_ctor_set(x_217, 2, x_214);
lean_ctor_set(x_217, 3, x_215);
lean_ctor_set(x_217, 4, x_179);
x_218 = lean_array_fset(x_211, x_190, x_217);
lean_dec(x_190);
if (lean_is_scalar(x_188)) {
 x_219 = lean_alloc_ctor(0, 5, 0);
} else {
 x_219 = x_188;
}
lean_ctor_set(x_219, 0, x_183);
lean_ctor_set(x_219, 1, x_184);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_186);
lean_ctor_set(x_219, 4, x_187);
lean_inc(x_1);
lean_inc(x_171);
x_220 = l_Lean_Meta_SynthInstance_tryResolve(x_173, x_171, x_181, x_1, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_221, 0);
lean_inc(x_226);
lean_dec(x_221);
x_227 = lean_ctor_get(x_220, 1);
lean_inc(x_227);
lean_dec(x_220);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
x_230 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_230, 0, x_171);
lean_ctor_set(x_230, 1, x_172);
lean_ctor_set(x_230, 2, x_228);
lean_ctor_set(x_230, 3, x_229);
x_231 = l_Lean_Meta_SynthInstance_consume(x_230, x_1, x_227);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_232 = lean_ctor_get(x_220, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_220, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_234 = x_220;
} else {
 lean_dec_ref(x_220);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
x_253 = lean_ctor_get(x_170, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_170, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_170, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_170, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_170, 4);
lean_inc(x_257);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 x_258 = x_170;
} else {
 lean_dec_ref(x_170);
 x_258 = lean_box(0);
}
x_259 = lean_array_pop(x_255);
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 5, 0);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_253);
lean_ctor_set(x_260, 1, x_254);
lean_ctor_set(x_260, 2, x_259);
lean_ctor_set(x_260, 3, x_256);
lean_ctor_set(x_260, 4, x_257);
x_261 = lean_box(0);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
}
}
lean_object* _init_l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_Consumernode_inhabited;
x_2 = l_Lean_Meta_SynthInstance_Answer_inhabited;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(x_3);
x_5 = lean_array_pop(x_3);
lean_ctor_set(x_1, 3, x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_12 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(x_10);
x_13 = lean_array_pop(x_10);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getNextToResume(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getNextToResume___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getNextToResume___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getNextToResume(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume found no remaining subgoals");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(426u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Meta_SynthInstance_resume___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resume");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" <== ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_resume___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_resume___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_resume(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Meta_SynthInstance_getNextToResume___rarg(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_Meta_SynthInstance_getEntry___closed__1;
x_9 = l_Lean_Meta_SynthInstance_resume___closed__2;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_2(x_10, x_1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_19);
x_21 = l_Lean_Meta_SynthInstance_tryAnswer(x_17, x_19, x_13, x_1, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_30 = x_21;
} else {
 lean_dec_ref(x_21);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
lean_inc(x_31);
lean_inc(x_15);
lean_ctor_set(x_5, 3, x_20);
lean_ctor_set(x_5, 2, x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_64; lean_object* x_65; uint8_t x_93; lean_object* x_94; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_35 = lean_ctor_get(x_33, 1);
lean_ctor_set(x_33, 1, x_31);
x_142 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_29);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_143, sizeof(void*)*1);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = 0;
x_93 = x_146;
x_94 = x_145;
goto block_141;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_dec(x_142);
x_148 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_149 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_148, x_1, x_147);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unbox(x_150);
lean_dec(x_150);
x_93 = x_152;
x_94 = x_151;
goto block_141;
}
block_63:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 1);
lean_dec(x_40);
lean_ctor_set(x_38, 1, x_35);
x_41 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_36);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 2);
x_44 = lean_ctor_get(x_38, 3);
x_45 = lean_ctor_get(x_38, 4);
x_46 = lean_ctor_get(x_38, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 2, x_43);
lean_ctor_set(x_47, 3, x_44);
lean_ctor_set(x_47, 4, x_45);
lean_ctor_set(x_47, 5, x_46);
lean_ctor_set(x_36, 0, x_47);
x_48 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_36);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
x_51 = lean_ctor_get(x_36, 2);
x_52 = lean_ctor_get(x_36, 3);
x_53 = lean_ctor_get(x_36, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_49, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_49, 5);
lean_inc(x_58);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 lean_ctor_release(x_49, 4);
 lean_ctor_release(x_49, 5);
 x_59 = x_49;
} else {
 lean_dec_ref(x_49);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 6, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_35);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_58);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_61, 2, x_51);
lean_ctor_set(x_61, 3, x_52);
lean_ctor_set(x_61, 4, x_53);
x_62 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_61);
return x_62;
}
}
block_92:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 1);
lean_dec(x_69);
lean_ctor_set(x_67, 1, x_35);
if (lean_is_scalar(x_30)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_30;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 2);
x_73 = lean_ctor_get(x_67, 3);
x_74 = lean_ctor_get(x_67, 4);
x_75 = lean_ctor_get(x_67, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_35);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_73);
lean_ctor_set(x_76, 4, x_74);
lean_ctor_set(x_76, 5, x_75);
lean_ctor_set(x_65, 0, x_76);
if (lean_is_scalar(x_30)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_30;
 lean_ctor_set_tag(x_77, 1);
}
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_65);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_65, 0);
x_79 = lean_ctor_get(x_65, 1);
x_80 = lean_ctor_get(x_65, 2);
x_81 = lean_ctor_get(x_65, 3);
x_82 = lean_ctor_get(x_65, 4);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_65);
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 5);
lean_inc(x_87);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 x_88 = x_78;
} else {
 lean_dec_ref(x_78);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 6, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_35);
lean_ctor_set(x_89, 2, x_84);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_86);
lean_ctor_set(x_89, 5, x_87);
x_90 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_79);
lean_ctor_set(x_90, 2, x_80);
lean_ctor_set(x_90, 3, x_81);
lean_ctor_set(x_90, 4, x_82);
if (lean_is_scalar(x_30)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_30;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_64);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
block_141:
{
if (x_93 == 0)
{
lean_dec(x_30);
lean_dec(x_19);
lean_dec(x_15);
x_36 = x_94;
goto block_63;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_1);
x_97 = l_Lean_Meta_inferType(x_15, x_1, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_1);
x_100 = l_Lean_Meta_inferType(x_19, x_1, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_30);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_ctor_set(x_94, 0, x_102);
x_103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_104 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_107 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_109 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_108, x_107, x_1, x_94);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_36 = x_110;
goto block_63;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_1);
x_111 = lean_ctor_get(x_100, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
lean_dec(x_100);
lean_ctor_set(x_94, 0, x_112);
x_64 = x_111;
x_65 = x_94;
goto block_92;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_5);
lean_dec(x_19);
lean_dec(x_1);
x_113 = lean_ctor_get(x_97, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_97, 1);
lean_inc(x_114);
lean_dec(x_97);
lean_ctor_set(x_94, 0, x_114);
x_64 = x_113;
x_65 = x_94;
goto block_92;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_94, 0);
x_116 = lean_ctor_get(x_94, 1);
x_117 = lean_ctor_get(x_94, 2);
x_118 = lean_ctor_get(x_94, 3);
x_119 = lean_ctor_get(x_94, 4);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_94);
lean_inc(x_1);
x_120 = l_Lean_Meta_inferType(x_15, x_1, x_115);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_1);
x_123 = l_Lean_Meta_inferType(x_19, x_1, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_30);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set(x_126, 4, x_119);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_121);
x_128 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_129 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_130, 0, x_124);
x_131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_133 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_132, x_131, x_1, x_126);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_36 = x_134;
goto block_63;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_121);
lean_dec(x_5);
lean_dec(x_1);
x_135 = lean_ctor_get(x_123, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_123, 1);
lean_inc(x_136);
lean_dec(x_123);
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_116);
lean_ctor_set(x_137, 2, x_117);
lean_ctor_set(x_137, 3, x_118);
lean_ctor_set(x_137, 4, x_119);
x_64 = x_135;
x_65 = x_137;
goto block_92;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_5);
lean_dec(x_19);
lean_dec(x_1);
x_138 = lean_ctor_get(x_120, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_120, 1);
lean_inc(x_139);
lean_dec(x_120);
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_116);
lean_ctor_set(x_140, 2, x_117);
lean_ctor_set(x_140, 3, x_118);
lean_ctor_set(x_140, 4, x_119);
x_64 = x_138;
x_65 = x_140;
goto block_92;
}
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_176; lean_object* x_177; uint8_t x_194; lean_object* x_195; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_153 = lean_ctor_get(x_33, 0);
x_154 = lean_ctor_get(x_33, 1);
x_155 = lean_ctor_get(x_33, 2);
x_156 = lean_ctor_get(x_33, 3);
x_157 = lean_ctor_get(x_33, 4);
x_158 = lean_ctor_get(x_33, 5);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_33);
x_224 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_224, 0, x_153);
lean_ctor_set(x_224, 1, x_31);
lean_ctor_set(x_224, 2, x_155);
lean_ctor_set(x_224, 3, x_156);
lean_ctor_set(x_224, 4, x_157);
lean_ctor_set(x_224, 5, x_158);
lean_ctor_set(x_29, 0, x_224);
x_225 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_29);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get_uint8(x_226, sizeof(void*)*1);
lean_dec(x_226);
if (x_227 == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = 0;
x_194 = x_229;
x_195 = x_228;
goto block_223;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_dec(x_225);
x_231 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_232 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_231, x_1, x_230);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_unbox(x_233);
lean_dec(x_233);
x_194 = x_235;
x_195 = x_234;
goto block_223;
}
block_175:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 4);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 lean_ctor_release(x_159, 2);
 lean_ctor_release(x_159, 3);
 lean_ctor_release(x_159, 4);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_160, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_160, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_160, 5);
lean_inc(x_170);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 x_171 = x_160;
} else {
 lean_dec_ref(x_160);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 6, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_166);
lean_ctor_set(x_172, 1, x_154);
lean_ctor_set(x_172, 2, x_167);
lean_ctor_set(x_172, 3, x_168);
lean_ctor_set(x_172, 4, x_169);
lean_ctor_set(x_172, 5, x_170);
if (lean_is_scalar(x_165)) {
 x_173 = lean_alloc_ctor(0, 5, 0);
} else {
 x_173 = x_165;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_161);
lean_ctor_set(x_173, 2, x_162);
lean_ctor_set(x_173, 3, x_163);
lean_ctor_set(x_173, 4, x_164);
x_174 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_173);
return x_174;
}
block_193:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 4);
lean_inc(x_182);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 lean_ctor_release(x_177, 4);
 x_183 = x_177;
} else {
 lean_dec_ref(x_177);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_178, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_178, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_178, 5);
lean_inc(x_188);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 lean_ctor_release(x_178, 5);
 x_189 = x_178;
} else {
 lean_dec_ref(x_178);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 6, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_184);
lean_ctor_set(x_190, 1, x_154);
lean_ctor_set(x_190, 2, x_185);
lean_ctor_set(x_190, 3, x_186);
lean_ctor_set(x_190, 4, x_187);
lean_ctor_set(x_190, 5, x_188);
if (lean_is_scalar(x_183)) {
 x_191 = lean_alloc_ctor(0, 5, 0);
} else {
 x_191 = x_183;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_179);
lean_ctor_set(x_191, 2, x_180);
lean_ctor_set(x_191, 3, x_181);
lean_ctor_set(x_191, 4, x_182);
if (lean_is_scalar(x_30)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_30;
 lean_ctor_set_tag(x_192, 1);
}
lean_ctor_set(x_192, 0, x_176);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
block_223:
{
if (x_194 == 0)
{
lean_dec(x_30);
lean_dec(x_19);
lean_dec(x_15);
x_159 = x_195;
goto block_175;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 4);
lean_inc(x_200);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 x_201 = x_195;
} else {
 lean_dec_ref(x_195);
 x_201 = lean_box(0);
}
lean_inc(x_1);
x_202 = l_Lean_Meta_inferType(x_15, x_1, x_196);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
lean_inc(x_1);
x_205 = l_Lean_Meta_inferType(x_19, x_1, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_30);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
if (lean_is_scalar(x_201)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_201;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_197);
lean_ctor_set(x_208, 2, x_198);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set(x_208, 4, x_200);
x_209 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_209, 0, x_203);
x_210 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_211 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_212, 0, x_206);
x_213 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_215 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_214, x_213, x_1, x_208);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_159 = x_216;
goto block_175;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_203);
lean_dec(x_5);
lean_dec(x_1);
x_217 = lean_ctor_get(x_205, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_205, 1);
lean_inc(x_218);
lean_dec(x_205);
if (lean_is_scalar(x_201)) {
 x_219 = lean_alloc_ctor(0, 5, 0);
} else {
 x_219 = x_201;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_197);
lean_ctor_set(x_219, 2, x_198);
lean_ctor_set(x_219, 3, x_199);
lean_ctor_set(x_219, 4, x_200);
x_176 = x_217;
x_177 = x_219;
goto block_193;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_5);
lean_dec(x_19);
lean_dec(x_1);
x_220 = lean_ctor_get(x_202, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_202, 1);
lean_inc(x_221);
lean_dec(x_202);
if (lean_is_scalar(x_201)) {
 x_222 = lean_alloc_ctor(0, 5, 0);
} else {
 x_222 = x_201;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_197);
lean_ctor_set(x_222, 2, x_198);
lean_ctor_set(x_222, 3, x_199);
lean_ctor_set(x_222, 4, x_200);
x_176 = x_220;
x_177 = x_222;
goto block_193;
}
}
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_265; lean_object* x_266; uint8_t x_283; lean_object* x_284; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_236 = lean_ctor_get(x_29, 0);
x_237 = lean_ctor_get(x_29, 1);
x_238 = lean_ctor_get(x_29, 2);
x_239 = lean_ctor_get(x_29, 3);
x_240 = lean_ctor_get(x_29, 4);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_29);
x_241 = lean_ctor_get(x_236, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_236, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_236, 3);
lean_inc(x_244);
x_245 = lean_ctor_get(x_236, 4);
lean_inc(x_245);
x_246 = lean_ctor_get(x_236, 5);
lean_inc(x_246);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 lean_ctor_release(x_236, 5);
 x_247 = x_236;
} else {
 lean_dec_ref(x_236);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_313 = lean_alloc_ctor(0, 6, 0);
} else {
 x_313 = x_247;
}
lean_ctor_set(x_313, 0, x_241);
lean_ctor_set(x_313, 1, x_31);
lean_ctor_set(x_313, 2, x_243);
lean_ctor_set(x_313, 3, x_244);
lean_ctor_set(x_313, 4, x_245);
lean_ctor_set(x_313, 5, x_246);
x_314 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_237);
lean_ctor_set(x_314, 2, x_238);
lean_ctor_set(x_314, 3, x_239);
lean_ctor_set(x_314, 4, x_240);
x_315 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_314);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get_uint8(x_316, sizeof(void*)*1);
lean_dec(x_316);
if (x_317 == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_dec(x_315);
x_319 = 0;
x_283 = x_319;
x_284 = x_318;
goto block_312;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_320 = lean_ctor_get(x_315, 1);
lean_inc(x_320);
lean_dec(x_315);
x_321 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_322 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_321, x_1, x_320);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_unbox(x_323);
lean_dec(x_323);
x_283 = x_325;
x_284 = x_324;
goto block_312;
}
block_264:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_248, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_248, 4);
lean_inc(x_253);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 lean_ctor_release(x_248, 2);
 lean_ctor_release(x_248, 3);
 lean_ctor_release(x_248, 4);
 x_254 = x_248;
} else {
 lean_dec_ref(x_248);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_249, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_249, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_249, 3);
lean_inc(x_257);
x_258 = lean_ctor_get(x_249, 4);
lean_inc(x_258);
x_259 = lean_ctor_get(x_249, 5);
lean_inc(x_259);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 lean_ctor_release(x_249, 4);
 lean_ctor_release(x_249, 5);
 x_260 = x_249;
} else {
 lean_dec_ref(x_249);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(0, 6, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_255);
lean_ctor_set(x_261, 1, x_242);
lean_ctor_set(x_261, 2, x_256);
lean_ctor_set(x_261, 3, x_257);
lean_ctor_set(x_261, 4, x_258);
lean_ctor_set(x_261, 5, x_259);
if (lean_is_scalar(x_254)) {
 x_262 = lean_alloc_ctor(0, 5, 0);
} else {
 x_262 = x_254;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_250);
lean_ctor_set(x_262, 2, x_251);
lean_ctor_set(x_262, 3, x_252);
lean_ctor_set(x_262, 4, x_253);
x_263 = l_Lean_Meta_SynthInstance_consume(x_5, x_1, x_262);
return x_263;
}
block_282:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_266, 3);
lean_inc(x_270);
x_271 = lean_ctor_get(x_266, 4);
lean_inc(x_271);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 lean_ctor_release(x_266, 2);
 lean_ctor_release(x_266, 3);
 lean_ctor_release(x_266, 4);
 x_272 = x_266;
} else {
 lean_dec_ref(x_266);
 x_272 = lean_box(0);
}
x_273 = lean_ctor_get(x_267, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_267, 2);
lean_inc(x_274);
x_275 = lean_ctor_get(x_267, 3);
lean_inc(x_275);
x_276 = lean_ctor_get(x_267, 4);
lean_inc(x_276);
x_277 = lean_ctor_get(x_267, 5);
lean_inc(x_277);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 lean_ctor_release(x_267, 2);
 lean_ctor_release(x_267, 3);
 lean_ctor_release(x_267, 4);
 lean_ctor_release(x_267, 5);
 x_278 = x_267;
} else {
 lean_dec_ref(x_267);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 6, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_273);
lean_ctor_set(x_279, 1, x_242);
lean_ctor_set(x_279, 2, x_274);
lean_ctor_set(x_279, 3, x_275);
lean_ctor_set(x_279, 4, x_276);
lean_ctor_set(x_279, 5, x_277);
if (lean_is_scalar(x_272)) {
 x_280 = lean_alloc_ctor(0, 5, 0);
} else {
 x_280 = x_272;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_268);
lean_ctor_set(x_280, 2, x_269);
lean_ctor_set(x_280, 3, x_270);
lean_ctor_set(x_280, 4, x_271);
if (lean_is_scalar(x_30)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_30;
 lean_ctor_set_tag(x_281, 1);
}
lean_ctor_set(x_281, 0, x_265);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
block_312:
{
if (x_283 == 0)
{
lean_dec(x_30);
lean_dec(x_19);
lean_dec(x_15);
x_248 = x_284;
goto block_264;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_284, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_284, 3);
lean_inc(x_288);
x_289 = lean_ctor_get(x_284, 4);
lean_inc(x_289);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 lean_ctor_release(x_284, 2);
 lean_ctor_release(x_284, 3);
 lean_ctor_release(x_284, 4);
 x_290 = x_284;
} else {
 lean_dec_ref(x_284);
 x_290 = lean_box(0);
}
lean_inc(x_1);
x_291 = l_Lean_Meta_inferType(x_15, x_1, x_285);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
lean_inc(x_1);
x_294 = l_Lean_Meta_inferType(x_19, x_1, x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_30);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
if (lean_is_scalar(x_290)) {
 x_297 = lean_alloc_ctor(0, 5, 0);
} else {
 x_297 = x_290;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_286);
lean_ctor_set(x_297, 2, x_287);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set(x_297, 4, x_289);
x_298 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_298, 0, x_292);
x_299 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_300 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_301, 0, x_295);
x_302 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_304 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_303, x_302, x_1, x_297);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_248 = x_305;
goto block_264;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_292);
lean_dec(x_5);
lean_dec(x_1);
x_306 = lean_ctor_get(x_294, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_294, 1);
lean_inc(x_307);
lean_dec(x_294);
if (lean_is_scalar(x_290)) {
 x_308 = lean_alloc_ctor(0, 5, 0);
} else {
 x_308 = x_290;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_286);
lean_ctor_set(x_308, 2, x_287);
lean_ctor_set(x_308, 3, x_288);
lean_ctor_set(x_308, 4, x_289);
x_265 = x_306;
x_266 = x_308;
goto block_282;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_5);
lean_dec(x_19);
lean_dec(x_1);
x_309 = lean_ctor_get(x_291, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_291, 1);
lean_inc(x_310);
lean_dec(x_291);
if (lean_is_scalar(x_290)) {
 x_311 = lean_alloc_ctor(0, 5, 0);
} else {
 x_311 = x_290;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_286);
lean_ctor_set(x_311, 2, x_287);
lean_ctor_set(x_311, 3, x_288);
lean_ctor_set(x_311, 4, x_289);
x_265 = x_309;
x_266 = x_311;
goto block_282;
}
}
}
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_326 = !lean_is_exclusive(x_21);
if (x_326 == 0)
{
return x_21;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_21, 0);
x_328 = lean_ctor_get(x_21, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_21);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_330 = lean_ctor_get(x_5, 0);
x_331 = lean_ctor_get(x_5, 1);
x_332 = lean_ctor_get(x_5, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_5);
x_333 = lean_ctor_get(x_6, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_6, 1);
lean_inc(x_334);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_333);
x_335 = l_Lean_Meta_SynthInstance_tryAnswer(x_332, x_333, x_13, x_1, x_12);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_1);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_338;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_337);
return x_340;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_375; lean_object* x_376; uint8_t x_393; lean_object* x_394; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
x_341 = lean_ctor_get(x_335, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_342 = x_335;
} else {
 lean_dec_ref(x_335);
 x_342 = lean_box(0);
}
x_343 = lean_ctor_get(x_336, 0);
lean_inc(x_343);
lean_dec(x_336);
lean_inc(x_343);
lean_inc(x_330);
x_344 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_344, 0, x_330);
lean_ctor_set(x_344, 1, x_331);
lean_ctor_set(x_344, 2, x_343);
lean_ctor_set(x_344, 3, x_334);
x_345 = lean_ctor_get(x_341, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_341, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_341, 2);
lean_inc(x_347);
x_348 = lean_ctor_get(x_341, 3);
lean_inc(x_348);
x_349 = lean_ctor_get(x_341, 4);
lean_inc(x_349);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 lean_ctor_release(x_341, 4);
 x_350 = x_341;
} else {
 lean_dec_ref(x_341);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_345, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_345, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_345, 2);
lean_inc(x_353);
x_354 = lean_ctor_get(x_345, 3);
lean_inc(x_354);
x_355 = lean_ctor_get(x_345, 4);
lean_inc(x_355);
x_356 = lean_ctor_get(x_345, 5);
lean_inc(x_356);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_357 = x_345;
} else {
 lean_dec_ref(x_345);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_423 = lean_alloc_ctor(0, 6, 0);
} else {
 x_423 = x_357;
}
lean_ctor_set(x_423, 0, x_351);
lean_ctor_set(x_423, 1, x_343);
lean_ctor_set(x_423, 2, x_353);
lean_ctor_set(x_423, 3, x_354);
lean_ctor_set(x_423, 4, x_355);
lean_ctor_set(x_423, 5, x_356);
if (lean_is_scalar(x_350)) {
 x_424 = lean_alloc_ctor(0, 5, 0);
} else {
 x_424 = x_350;
}
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_346);
lean_ctor_set(x_424, 2, x_347);
lean_ctor_set(x_424, 3, x_348);
lean_ctor_set(x_424, 4, x_349);
x_425 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_424);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get_uint8(x_426, sizeof(void*)*1);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; uint8_t x_429; 
x_428 = lean_ctor_get(x_425, 1);
lean_inc(x_428);
lean_dec(x_425);
x_429 = 0;
x_393 = x_429;
x_394 = x_428;
goto block_422;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_430 = lean_ctor_get(x_425, 1);
lean_inc(x_430);
lean_dec(x_425);
x_431 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_432 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_431, x_1, x_430);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_unbox(x_433);
lean_dec(x_433);
x_393 = x_435;
x_394 = x_434;
goto block_422;
}
block_374:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_358, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_358, 3);
lean_inc(x_362);
x_363 = lean_ctor_get(x_358, 4);
lean_inc(x_363);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 lean_ctor_release(x_358, 4);
 x_364 = x_358;
} else {
 lean_dec_ref(x_358);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_359, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_359, 2);
lean_inc(x_366);
x_367 = lean_ctor_get(x_359, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_359, 4);
lean_inc(x_368);
x_369 = lean_ctor_get(x_359, 5);
lean_inc(x_369);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 lean_ctor_release(x_359, 2);
 lean_ctor_release(x_359, 3);
 lean_ctor_release(x_359, 4);
 lean_ctor_release(x_359, 5);
 x_370 = x_359;
} else {
 lean_dec_ref(x_359);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 6, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_365);
lean_ctor_set(x_371, 1, x_352);
lean_ctor_set(x_371, 2, x_366);
lean_ctor_set(x_371, 3, x_367);
lean_ctor_set(x_371, 4, x_368);
lean_ctor_set(x_371, 5, x_369);
if (lean_is_scalar(x_364)) {
 x_372 = lean_alloc_ctor(0, 5, 0);
} else {
 x_372 = x_364;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_360);
lean_ctor_set(x_372, 2, x_361);
lean_ctor_set(x_372, 3, x_362);
lean_ctor_set(x_372, 4, x_363);
x_373 = l_Lean_Meta_SynthInstance_consume(x_344, x_1, x_372);
return x_373;
}
block_392:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_376, 2);
lean_inc(x_379);
x_380 = lean_ctor_get(x_376, 3);
lean_inc(x_380);
x_381 = lean_ctor_get(x_376, 4);
lean_inc(x_381);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 lean_ctor_release(x_376, 4);
 x_382 = x_376;
} else {
 lean_dec_ref(x_376);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_377, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_377, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_377, 3);
lean_inc(x_385);
x_386 = lean_ctor_get(x_377, 4);
lean_inc(x_386);
x_387 = lean_ctor_get(x_377, 5);
lean_inc(x_387);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 lean_ctor_release(x_377, 4);
 lean_ctor_release(x_377, 5);
 x_388 = x_377;
} else {
 lean_dec_ref(x_377);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(0, 6, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_383);
lean_ctor_set(x_389, 1, x_352);
lean_ctor_set(x_389, 2, x_384);
lean_ctor_set(x_389, 3, x_385);
lean_ctor_set(x_389, 4, x_386);
lean_ctor_set(x_389, 5, x_387);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(0, 5, 0);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_378);
lean_ctor_set(x_390, 2, x_379);
lean_ctor_set(x_390, 3, x_380);
lean_ctor_set(x_390, 4, x_381);
if (lean_is_scalar(x_342)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_342;
 lean_ctor_set_tag(x_391, 1);
}
lean_ctor_set(x_391, 0, x_375);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
block_422:
{
if (x_393 == 0)
{
lean_dec(x_342);
lean_dec(x_333);
lean_dec(x_330);
x_358 = x_394;
goto block_374;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
x_397 = lean_ctor_get(x_394, 2);
lean_inc(x_397);
x_398 = lean_ctor_get(x_394, 3);
lean_inc(x_398);
x_399 = lean_ctor_get(x_394, 4);
lean_inc(x_399);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 lean_ctor_release(x_394, 2);
 lean_ctor_release(x_394, 3);
 lean_ctor_release(x_394, 4);
 x_400 = x_394;
} else {
 lean_dec_ref(x_394);
 x_400 = lean_box(0);
}
lean_inc(x_1);
x_401 = l_Lean_Meta_inferType(x_330, x_1, x_395);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
lean_inc(x_1);
x_404 = l_Lean_Meta_inferType(x_333, x_1, x_403);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_342);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
if (lean_is_scalar(x_400)) {
 x_407 = lean_alloc_ctor(0, 5, 0);
} else {
 x_407 = x_400;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_396);
lean_ctor_set(x_407, 2, x_397);
lean_ctor_set(x_407, 3, x_398);
lean_ctor_set(x_407, 4, x_399);
x_408 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_408, 0, x_402);
x_409 = l_Lean_Meta_SynthInstance_resume___closed__7;
x_410 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
x_411 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_411, 0, x_405);
x_412 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
x_413 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_414 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_413, x_412, x_1, x_407);
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_358 = x_415;
goto block_374;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_402);
lean_dec(x_344);
lean_dec(x_1);
x_416 = lean_ctor_get(x_404, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_404, 1);
lean_inc(x_417);
lean_dec(x_404);
if (lean_is_scalar(x_400)) {
 x_418 = lean_alloc_ctor(0, 5, 0);
} else {
 x_418 = x_400;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_396);
lean_ctor_set(x_418, 2, x_397);
lean_ctor_set(x_418, 3, x_398);
lean_ctor_set(x_418, 4, x_399);
x_375 = x_416;
x_376 = x_418;
goto block_392;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_344);
lean_dec(x_333);
lean_dec(x_1);
x_419 = lean_ctor_get(x_401, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_401, 1);
lean_inc(x_420);
lean_dec(x_401);
if (lean_is_scalar(x_400)) {
 x_421 = lean_alloc_ctor(0, 5, 0);
} else {
 x_421 = x_400;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_396);
lean_ctor_set(x_421, 2, x_397);
lean_ctor_set(x_421, 3, x_398);
lean_ctor_set(x_421, 4, x_399);
x_375 = x_419;
x_376 = x_421;
goto block_392;
}
}
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_1);
x_436 = lean_ctor_get(x_335, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_335, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_438 = x_335;
} else {
 lean_dec_ref(x_335);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_step(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = l_Array_isEmpty___rarg(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SynthInstance_resume(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = l_Array_isEmpty___rarg(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_SynthInstance_generate(x_1, x_2);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
return x_35;
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_getResult___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_SynthInstance_getResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_getResult___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_getResult___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SynthInstance_getResult(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("remaining fuel ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthInstance is out of fuel");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_synth___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_synth___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_synth___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_57; lean_object* x_58; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_68 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_69, sizeof(void*)*1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = 0;
x_57 = x_72;
x_58 = x_71;
goto block_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_74 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_75 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_74, x_2, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
x_57 = x_78;
x_58 = x_77;
goto block_67;
}
block_56:
{
lean_object* x_9; 
lean_inc(x_2);
x_9 = l_Lean_Meta_SynthInstance_step(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_23 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_22, x_2, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
lean_ctor_set(x_23, 0, x_13);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l_Lean_Meta_SynthInstance_synth___main___closed__3;
x_32 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_22, x_31, x_2, x_30);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_13);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = l_Lean_Meta_SynthInstance_getResult___rarg(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_1 = x_7;
x_3 = x_40;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_38, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_38, 0, x_46);
return x_38;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_49 = x_39;
} else {
 lean_dec_ref(x_39);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
return x_9;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_9, 0);
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_9);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
block_67:
{
if (x_57 == 0)
{
x_8 = x_58;
goto block_56;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_inc(x_7);
x_59 = l_Nat_repr(x_7);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_Meta_SynthInstance_synth___main___closed__6;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_65 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_64, x_63, x_2, x_58);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_8 = x_66;
goto block_56;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = l_Lean_Meta_SynthInstance_getTraceState___rarg(x_3);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_81, sizeof(void*)*1);
lean_dec(x_81);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_80);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_80, 0);
lean_dec(x_84);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_dec(x_80);
x_88 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_89 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_SynthInstance_newSubgoal___spec__7(x_88, x_2, x_87);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_89, 0);
lean_dec(x_93);
lean_ctor_set(x_89, 0, x_79);
return x_89;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_79);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = l_Lean_Meta_SynthInstance_synth___main___closed__9;
x_98 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_SynthInstance_newSubgoal___spec__8(x_88, x_97, x_2, x_96);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_79);
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_79);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
}
lean_object* l_Lean_Meta_SynthInstance_synth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SynthInstance_synth___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_mkHashMap___at_Lean_Meta_SynthInstance_main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("main goal ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_SynthInstance_main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SynthInstance_main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SynthInstance_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_4, 4);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_266, sizeof(void*)*1);
lean_dec(x_266);
if (x_267 == 0)
{
uint8_t x_268; 
x_268 = 0;
x_5 = x_268;
x_6 = x_4;
goto block_265;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_269 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_270 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_269, x_3, x_4);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_unbox(x_271);
lean_dec(x_271);
x_5 = x_273;
x_6 = x_272;
goto block_265;
}
block_265:
{
if (x_5 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_11 = 0;
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_11);
x_33 = lean_box(0);
x_34 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Lean_Meta_mkFreshExprMVar(x_1, x_33, x_34, x_3, x_6);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_inc(x_38);
x_39 = l_Lean_Meta_SynthInstance_mkTableKey(x_38, x_1);
x_40 = lean_box(0);
x_41 = l_Array_empty___closed__1;
x_42 = l_Lean_Meta_SynthInstance_main___closed__1;
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_box(1);
lean_inc(x_3);
x_45 = l_Lean_Meta_SynthInstance_newSubgoal(x_38, x_39, x_36, x_44, x_3, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 4);
lean_inc(x_50);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_47, 1);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_49, 4);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_10);
lean_ctor_set(x_47, 1, x_49);
return x_47;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_10);
lean_ctor_set(x_49, 4, x_57);
lean_ctor_set(x_47, 1, x_49);
return x_47;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
x_60 = lean_ctor_get(x_49, 2);
x_61 = lean_ctor_get(x_49, 3);
x_62 = lean_ctor_get(x_49, 5);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_64 = x_50;
} else {
 lean_dec_ref(x_50);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 1, 1);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_10);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_59);
lean_ctor_set(x_66, 2, x_60);
lean_ctor_set(x_66, 3, x_61);
lean_ctor_set(x_66, 4, x_65);
lean_ctor_set(x_66, 5, x_62);
lean_ctor_set(x_47, 1, x_66);
return x_47;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_ctor_get(x_49, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_49, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_49, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_49, 5);
lean_inc(x_72);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 lean_ctor_release(x_49, 4);
 lean_ctor_release(x_49, 5);
 x_73 = x_49;
} else {
 lean_dec_ref(x_49);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_50, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_75 = x_50;
} else {
 lean_dec_ref(x_50);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_10);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_71);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_47, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_47, 1);
lean_inc(x_80);
lean_dec(x_47);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_12 = x_79;
x_13 = x_81;
goto block_32;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_ctor_get(x_45, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_45, 1);
lean_inc(x_83);
lean_dec(x_45);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_12 = x_82;
x_13 = x_84;
goto block_32;
}
block_32:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 4);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_10);
lean_ctor_set(x_13, 4, x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_ctor_get(x_13, 2);
x_25 = lean_ctor_get(x_13, 3);
x_26 = lean_ctor_get(x_13, 5);
lean_inc(x_26);
lean_inc(x_21);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_28 = x_21;
} else {
 lean_dec_ref(x_21);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 1, 1);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_10);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_26);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_85 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_86 = lean_ctor_get(x_8, 0);
lean_inc(x_86);
lean_dec(x_8);
x_87 = 0;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
lean_ctor_set(x_6, 4, x_88);
x_104 = lean_box(0);
x_105 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_106 = l_Lean_Meta_mkFreshExprMVar(x_1, x_104, x_105, x_3, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_inc(x_109);
x_110 = l_Lean_Meta_SynthInstance_mkTableKey(x_109, x_1);
x_111 = lean_box(0);
x_112 = l_Array_empty___closed__1;
x_113 = l_Lean_Meta_SynthInstance_main___closed__1;
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_111);
lean_ctor_set(x_114, 2, x_112);
lean_ctor_set(x_114, 3, x_112);
lean_ctor_set(x_114, 4, x_113);
x_115 = lean_box(1);
lean_inc(x_3);
x_116 = l_Lean_Meta_SynthInstance_newSubgoal(x_109, x_110, x_107, x_115, x_3, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_ctor_get(x_120, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_120, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 5);
lean_inc(x_128);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 x_129 = x_120;
} else {
 lean_dec_ref(x_120);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_121, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_131 = x_121;
} else {
 lean_dec_ref(x_121);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 1, 1);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_85);
if (lean_is_scalar(x_129)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_129;
}
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_127);
lean_ctor_set(x_133, 4, x_132);
lean_ctor_set(x_133, 5, x_128);
if (lean_is_scalar(x_123)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_123;
}
lean_ctor_set(x_134, 0, x_122);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_118, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_118, 1);
lean_inc(x_136);
lean_dec(x_118);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
x_89 = x_135;
x_90 = x_137;
goto block_103;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_3);
lean_dec(x_2);
x_138 = lean_ctor_get(x_116, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_116, 1);
lean_inc(x_139);
lean_dec(x_116);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_89 = x_138;
x_90 = x_140;
goto block_103;
}
block_103:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = lean_ctor_get(x_90, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 5);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 lean_ctor_release(x_90, 5);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_99 = x_91;
} else {
 lean_dec_ref(x_91);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 1, 1);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_85);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(0, 6, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_94);
lean_ctor_set(x_101, 3, x_95);
lean_ctor_set(x_101, 4, x_100);
lean_ctor_set(x_101, 5, x_96);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_141 = lean_ctor_get(x_6, 4);
x_142 = lean_ctor_get(x_6, 0);
x_143 = lean_ctor_get(x_6, 1);
x_144 = lean_ctor_get(x_6, 2);
x_145 = lean_ctor_get(x_6, 3);
x_146 = lean_ctor_get(x_6, 5);
lean_inc(x_146);
lean_inc(x_141);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_6);
x_147 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
x_148 = lean_ctor_get(x_141, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
 x_149 = lean_box(0);
}
x_150 = 0;
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 1, 1);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
x_152 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_152, 0, x_142);
lean_ctor_set(x_152, 1, x_143);
lean_ctor_set(x_152, 2, x_144);
lean_ctor_set(x_152, 3, x_145);
lean_ctor_set(x_152, 4, x_151);
lean_ctor_set(x_152, 5, x_146);
x_168 = lean_box(0);
x_169 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_170 = l_Lean_Meta_mkFreshExprMVar(x_1, x_168, x_169, x_3, x_152);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_inc(x_173);
x_174 = l_Lean_Meta_SynthInstance_mkTableKey(x_173, x_1);
x_175 = lean_box(0);
x_176 = l_Array_empty___closed__1;
x_177 = l_Lean_Meta_SynthInstance_main___closed__1;
x_178 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_176);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set(x_178, 4, x_177);
x_179 = lean_box(1);
lean_inc(x_3);
x_180 = l_Lean_Meta_SynthInstance_newSubgoal(x_173, x_174, x_171, x_179, x_3, x_178);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_184, 4);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_187 = x_182;
} else {
 lean_dec_ref(x_182);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 5);
lean_inc(x_192);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 x_193 = x_184;
} else {
 lean_dec_ref(x_184);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_185, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_195 = x_185;
} else {
 lean_dec_ref(x_185);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 1, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_193)) {
 x_197 = lean_alloc_ctor(0, 6, 0);
} else {
 x_197 = x_193;
}
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_189);
lean_ctor_set(x_197, 2, x_190);
lean_ctor_set(x_197, 3, x_191);
lean_ctor_set(x_197, 4, x_196);
lean_ctor_set(x_197, 5, x_192);
if (lean_is_scalar(x_187)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_187;
}
lean_ctor_set(x_198, 0, x_186);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_182, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_182, 1);
lean_inc(x_200);
lean_dec(x_182);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_153 = x_199;
x_154 = x_201;
goto block_167;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_3);
lean_dec(x_2);
x_202 = lean_ctor_get(x_180, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_180, 1);
lean_inc(x_203);
lean_dec(x_180);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
x_153 = x_202;
x_154 = x_204;
goto block_167;
}
block_167:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_154, 4);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 5);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 lean_ctor_release(x_154, 5);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_155, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_163 = x_155;
} else {
 lean_dec_ref(x_155);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 1, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_147);
if (lean_is_scalar(x_161)) {
 x_165 = lean_alloc_ctor(0, 6, 0);
} else {
 x_165 = x_161;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_157);
lean_ctor_set(x_165, 2, x_158);
lean_ctor_set(x_165, 3, x_159);
lean_ctor_set(x_165, 4, x_164);
lean_ctor_set(x_165, 5, x_160);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_252; uint8_t x_253; 
x_205 = l___private_Lean_Util_Trace_3__getResetTraces___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__6___rarg(x_6);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_252 = lean_ctor_get(x_207, 4);
lean_inc(x_252);
x_253 = lean_ctor_get_uint8(x_252, sizeof(void*)*1);
lean_dec(x_252);
if (x_253 == 0)
{
x_208 = x_207;
goto block_251;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_254 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_255 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_254, x_3, x_207);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_unbox(x_256);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
lean_dec(x_255);
x_208 = x_258;
goto block_251;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
lean_inc(x_1);
x_260 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_260, 0, x_1);
x_261 = l_Lean_Meta_SynthInstance_main___closed__4;
x_262 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_254, x_262, x_3, x_259);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_208 = x_264;
goto block_251;
}
}
block_251:
{
lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_209 = lean_box(0);
x_210 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_211 = l_Lean_Meta_mkFreshExprMVar(x_1, x_209, x_210, x_3, x_208);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_inc(x_214);
x_215 = l_Lean_Meta_SynthInstance_mkTableKey(x_214, x_1);
x_216 = lean_box(0);
x_217 = l_Array_empty___closed__1;
x_218 = l_Lean_Meta_SynthInstance_main___closed__1;
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_213);
lean_ctor_set(x_219, 1, x_216);
lean_ctor_set(x_219, 2, x_217);
lean_ctor_set(x_219, 3, x_217);
lean_ctor_set(x_219, 4, x_218);
x_220 = lean_box(1);
lean_inc(x_3);
x_221 = l_Lean_Meta_SynthInstance_newSubgoal(x_214, x_215, x_212, x_220, x_3, x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
lean_inc(x_3);
x_223 = l_Lean_Meta_SynthInstance_synth___main(x_2, x_3, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec(x_225);
x_227 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_228 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_206, x_227, x_3, x_226);
lean_dec(x_3);
x_229 = !lean_is_exclusive(x_228);
if (x_229 == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_228, 0);
lean_dec(x_230);
lean_ctor_set(x_228, 0, x_224);
return x_228;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_224);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_233 = lean_ctor_get(x_223, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_223, 1);
lean_inc(x_234);
lean_dec(x_223);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec(x_234);
x_236 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_237 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_206, x_236, x_3, x_235);
lean_dec(x_3);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_237, 0);
lean_dec(x_239);
lean_ctor_set_tag(x_237, 1);
lean_ctor_set(x_237, 0, x_233);
return x_237;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_233);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
lean_dec(x_2);
x_242 = lean_ctor_get(x_221, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_221, 1);
lean_inc(x_243);
lean_dec(x_221);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec(x_243);
x_245 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_246 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_206, x_245, x_3, x_244);
lean_dec(x_3);
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_246, 0);
lean_dec(x_248);
lean_ctor_set_tag(x_246, 1);
lean_ctor_set(x_246, 0, x_242);
return x_246;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_242);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_whnf(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_mkForall(x_1, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* _init_l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_2__preprocess___lambda__1), 4, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_2__preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1;
x_5 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Meta_instantiateLevelMVars(x_7, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Level_hasMVar(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_10);
x_1 = x_2;
x_2 = x_8;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
x_14 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_15);
x_1 = x_2;
x_2 = x_8;
x_4 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = l_Lean_Meta_instantiateLevelMVars(x_18, x_3, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Level_hasMVar(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_1);
x_1 = x_24;
x_2 = x_19;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_26 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_1);
x_1 = x_29;
x_2 = x_19;
x_4 = x_28;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocessLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(x_4, x_1, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_List_reverse___rarg(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_List_reverse___rarg(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldlM___main___at___private_Lean_Meta_SynthInstance_3__preprocessLevels___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_3__preprocessLevels___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_SynthInstance_3__preprocessLevels(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type class resolution failed, insufficient number of arguments");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1;
x_2 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf(x_1, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_array_fget(x_3, x_2);
lean_inc(x_12);
x_15 = lean_is_out_param(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_inc(x_14);
x_16 = lean_array_fset(x_3, x_2, x_14);
x_17 = lean_expr_instantiate1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_19;
x_3 = x_16;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = 0;
lean_inc(x_4);
x_23 = l_Lean_Meta_mkFreshExprMVar(x_12, x_21, x_22, x_4, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = lean_array_fset(x_3, x_2, x_24);
x_27 = lean_expr_instantiate1(x_13, x_24);
lean_dec(x_24);
lean_dec(x_13);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
lean_dec(x_2);
x_1 = x_27;
x_2 = x_29;
x_3 = x_26;
x_5 = x_25;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_9, 0);
lean_dec(x_32);
x_33 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_33);
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
x_35 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_4__preprocessArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn___main(x_3);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_inc(x_7);
x_10 = lean_has_out_params(x_9, x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_3__getAppArgsAux___main(x_3, x_15, x_17);
x_19 = l___private_Lean_Meta_SynthInstance_3__preprocessLevels(x_8, x_4, x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkConst(x_7, x_20);
lean_inc(x_4);
lean_inc(x_22);
x_23 = l_Lean_Meta_inferType(x_22, x_4, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_4);
x_26 = l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main(x_24, x_12, x_18, x_4, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_12, x_22);
lean_dec(x_27);
x_30 = l_Lean_Meta_mkForall(x_2, x_29, x_4, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_2);
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
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
}
lean_object* l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_SynthInstance_5__preprocessOutParam___lambda__1), 5, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Meta_forallTelescope___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxSteps");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__73;
x_2 = l_Lean_Meta_maxStepsOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10000u);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum steps for the type class instance synthesis procedure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_maxStepsOption___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_maxStepsOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Meta_maxStepsOption___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_maxStepsOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_maxStepsOption___closed__2;
x_3 = l_Lean_Meta_maxStepsOption___closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_6__getMaxSteps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_maxStepsOption___closed__2;
x_3 = lean_unsigned_to_nat(10000u);
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_6__getMaxSteps___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_SynthInstance_6__getMaxSteps(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_eqv(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_eqv(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Meta_synthInstance_x3f___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Expr_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_expr_eqv(x_5, x_9);
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_13 = lean_expr_eqv(x_3, x_11);
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
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(x_3, x_4, x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("FOUND result ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ==> ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_synthInstance_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_synthInstance_x3f___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
x_15 = l___private_Lean_Meta_SynthInstance_6__getMaxSteps(x_10);
x_16 = 1;
x_17 = 2;
x_18 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 2, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 3, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 4, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 5, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 6, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set(x_2, 0, x_18);
x_19 = l_Lean_Meta_instantiateMVars(x_1, x_2, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_inc(x_2);
x_24 = l_Lean_Meta_forallTelescopeReducing___rarg(x_20, x_23, x_2, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_61 = lean_ctor_get(x_26, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_26, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_26, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_26, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_26, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_26, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_67, x_25);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_26);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_164; lean_object* x_165; lean_object* x_177; lean_object* x_178; 
x_70 = lean_ctor_get(x_26, 5);
lean_dec(x_70);
x_71 = lean_ctor_get(x_26, 4);
lean_dec(x_71);
x_72 = lean_ctor_get(x_26, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_26, 2);
lean_dec(x_73);
x_74 = lean_ctor_get(x_26, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_26, 0);
lean_dec(x_75);
lean_inc(x_62);
x_177 = l_Lean_MetavarContext_incDepth(x_62);
lean_ctor_set(x_26, 1, x_177);
lean_inc(x_2);
lean_inc(x_25);
x_178 = l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(x_25, x_2, x_26);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_216; uint8_t x_217; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_216 = lean_ctor_get(x_180, 4);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_216, sizeof(void*)*1);
lean_dec(x_216);
if (x_217 == 0)
{
x_181 = x_180;
goto block_215;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_218 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_219 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_218, x_2, x_180);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_unbox(x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_181 = x_222;
goto block_215;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_223 = lean_ctor_get(x_219, 1);
lean_inc(x_223);
lean_dec(x_219);
lean_inc(x_25);
x_224 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_224, 0, x_25);
x_225 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_226 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_179);
x_227 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_227, 0, x_179);
x_228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_218, x_228, x_2, x_223);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_181 = x_230;
goto block_215;
}
}
block_215:
{
lean_object* x_182; 
lean_inc(x_2);
x_182 = l_Lean_Meta_SynthInstance_main(x_179, x_15, x_2, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
lean_dec(x_22);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_76 = x_183;
x_77 = x_184;
goto block_163;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_200; uint8_t x_201; 
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_187 = x_183;
} else {
 lean_dec_ref(x_183);
 x_187 = lean_box(0);
}
x_200 = lean_ctor_get(x_185, 4);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_200, sizeof(void*)*1);
lean_dec(x_200);
if (x_201 == 0)
{
x_188 = x_185;
goto block_199;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_202 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_203 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_202, x_2, x_185);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_unbox(x_204);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
x_188 = x_206;
goto block_199;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
lean_dec(x_203);
lean_inc(x_186);
x_208 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_208, 0, x_186);
x_209 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_210 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_202, x_210, x_2, x_207);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_188 = x_212;
goto block_199;
}
}
block_199:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_189 = l_Lean_Meta_instantiateMVars(x_186, x_2, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Meta_hasAssignableMVar(x_190, x_2, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
lean_dec(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
if (lean_is_scalar(x_187)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_187;
}
lean_ctor_set(x_196, 0, x_190);
x_76 = x_196;
x_77 = x_195;
goto block_163;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_190);
lean_dec(x_187);
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_box(0);
x_76 = x_198;
x_77 = x_197;
goto block_163;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_213 = lean_ctor_get(x_182, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_182, 1);
lean_inc(x_214);
lean_dec(x_182);
x_164 = x_213;
x_165 = x_214;
goto block_176;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_231 = lean_ctor_get(x_178, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_178, 1);
lean_inc(x_232);
lean_dec(x_178);
x_164 = x_231;
x_165 = x_232;
goto block_176;
}
block_163:
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 4);
x_80 = lean_ctor_get(x_77, 1);
lean_dec(x_80);
lean_inc(x_79);
lean_ctor_set(x_77, 1, x_62);
if (lean_obj_tag(x_76) == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_76;
x_29 = x_77;
goto block_60;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_107; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
 x_82 = lean_box(0);
}
x_107 = lean_ctor_get_uint8(x_79, sizeof(void*)*1);
lean_dec(x_79);
if (x_107 == 0)
{
x_83 = x_77;
goto block_106;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_109 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_108, x_2, x_77);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_83 = x_112;
goto block_106;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec(x_109);
lean_inc(x_81);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_81);
x_115 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_116 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_108, x_116, x_2, x_113);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_83 = x_118;
goto block_106;
}
}
block_106:
{
lean_object* x_84; 
lean_inc(x_2);
lean_inc(x_81);
x_84 = l_Lean_Meta_inferType(x_81, x_2, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_5);
lean_ctor_set(x_87, 1, x_6);
lean_ctor_set(x_87, 2, x_7);
lean_ctor_set(x_87, 3, x_8);
lean_ctor_set(x_87, 4, x_9);
lean_inc(x_25);
x_88 = l_Lean_Meta_isExprDefEq(x_25, x_85, x_87, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_2);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_box(0);
x_28 = x_92;
x_29 = x_91;
goto block_60;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_dec(x_88);
x_94 = l_Lean_Meta_instantiateMVars(x_81, x_2, x_93);
lean_dec(x_2);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
if (lean_is_scalar(x_82)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_82;
}
lean_ctor_set(x_97, 0, x_95);
x_28 = x_97;
x_29 = x_96;
goto block_60;
}
}
else
{
uint8_t x_98; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_88);
if (x_98 == 0)
{
return x_88;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_88, 0);
x_100 = lean_ctor_get(x_88, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_88);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_102 = !lean_is_exclusive(x_84);
if (x_102 == 0)
{
return x_84;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_84, 0);
x_104 = lean_ctor_get(x_84, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_84);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_77, 0);
x_120 = lean_ctor_get(x_77, 2);
x_121 = lean_ctor_get(x_77, 3);
x_122 = lean_ctor_get(x_77, 4);
x_123 = lean_ctor_get(x_77, 5);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_77);
lean_inc(x_122);
x_124 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_62);
lean_ctor_set(x_124, 2, x_120);
lean_ctor_set(x_124, 3, x_121);
lean_ctor_set(x_124, 4, x_122);
lean_ctor_set(x_124, 5, x_123);
if (lean_obj_tag(x_76) == 0)
{
lean_dec(x_122);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_76;
x_29 = x_124;
goto block_60;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_151; 
x_125 = lean_ctor_get(x_76, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_126 = x_76;
} else {
 lean_dec_ref(x_76);
 x_126 = lean_box(0);
}
x_151 = lean_ctor_get_uint8(x_122, sizeof(void*)*1);
lean_dec(x_122);
if (x_151 == 0)
{
x_127 = x_124;
goto block_150;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_153 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_152, x_2, x_124);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_127 = x_156;
goto block_150;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
lean_inc(x_125);
x_158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_158, 0, x_125);
x_159 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_160 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_152, x_160, x_2, x_157);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_127 = x_162;
goto block_150;
}
}
block_150:
{
lean_object* x_128; 
lean_inc(x_2);
lean_inc(x_125);
x_128 = l_Lean_Meta_inferType(x_125, x_2, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_5);
lean_ctor_set(x_131, 1, x_6);
lean_ctor_set(x_131, 2, x_7);
lean_ctor_set(x_131, 3, x_8);
lean_ctor_set(x_131, 4, x_9);
lean_inc(x_25);
x_132 = l_Lean_Meta_isExprDefEq(x_25, x_129, x_131, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_2);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_box(0);
x_28 = x_136;
x_29 = x_135;
goto block_60;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_dec(x_132);
x_138 = l_Lean_Meta_instantiateMVars(x_125, x_2, x_137);
lean_dec(x_2);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
if (lean_is_scalar(x_126)) {
 x_141 = lean_alloc_ctor(1, 1, 0);
} else {
 x_141 = x_126;
}
lean_ctor_set(x_141, 0, x_139);
x_28 = x_141;
x_29 = x_140;
goto block_60;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_142 = lean_ctor_get(x_132, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_132, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_144 = x_132;
} else {
 lean_dec_ref(x_132);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_146 = lean_ctor_get(x_128, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_148 = x_128;
} else {
 lean_dec_ref(x_128);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
}
block_176:
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_165, 1);
lean_dec(x_167);
lean_ctor_set(x_165, 1, x_62);
if (lean_is_scalar(x_22)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_22;
 lean_ctor_set_tag(x_168, 1);
}
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_165);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_165, 0);
x_170 = lean_ctor_get(x_165, 2);
x_171 = lean_ctor_get(x_165, 3);
x_172 = lean_ctor_get(x_165, 4);
x_173 = lean_ctor_get(x_165, 5);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_165);
x_174 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_174, 0, x_169);
lean_ctor_set(x_174, 1, x_62);
lean_ctor_set(x_174, 2, x_170);
lean_ctor_set(x_174, 3, x_171);
lean_ctor_set(x_174, 4, x_172);
lean_ctor_set(x_174, 5, x_173);
if (lean_is_scalar(x_22)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_22;
 lean_ctor_set_tag(x_175, 1);
}
lean_ctor_set(x_175, 0, x_164);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_281; lean_object* x_282; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_26);
lean_inc(x_62);
x_292 = l_Lean_MetavarContext_incDepth(x_62);
x_293 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_293, 0, x_61);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_293, 2, x_63);
lean_ctor_set(x_293, 3, x_64);
lean_ctor_set(x_293, 4, x_65);
lean_ctor_set(x_293, 5, x_66);
lean_inc(x_2);
lean_inc(x_25);
x_294 = l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(x_25, x_2, x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_332; uint8_t x_333; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_332 = lean_ctor_get(x_296, 4);
lean_inc(x_332);
x_333 = lean_ctor_get_uint8(x_332, sizeof(void*)*1);
lean_dec(x_332);
if (x_333 == 0)
{
x_297 = x_296;
goto block_331;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_334 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_335 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_334, x_2, x_296);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_unbox(x_336);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
lean_dec(x_335);
x_297 = x_338;
goto block_331;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_339 = lean_ctor_get(x_335, 1);
lean_inc(x_339);
lean_dec(x_335);
lean_inc(x_25);
x_340 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_340, 0, x_25);
x_341 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_342 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
lean_inc(x_295);
x_343 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_343, 0, x_295);
x_344 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
x_345 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_334, x_344, x_2, x_339);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
lean_dec(x_345);
x_297 = x_346;
goto block_331;
}
}
block_331:
{
lean_object* x_298; 
lean_inc(x_2);
x_298 = l_Lean_Meta_SynthInstance_main(x_295, x_15, x_2, x_297);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; 
lean_dec(x_22);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_233 = x_299;
x_234 = x_300;
goto block_280;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_316; uint8_t x_317; 
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_ctor_get(x_299, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 x_303 = x_299;
} else {
 lean_dec_ref(x_299);
 x_303 = lean_box(0);
}
x_316 = lean_ctor_get(x_301, 4);
lean_inc(x_316);
x_317 = lean_ctor_get_uint8(x_316, sizeof(void*)*1);
lean_dec(x_316);
if (x_317 == 0)
{
x_304 = x_301;
goto block_315;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_318 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_319 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_318, x_2, x_301);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_unbox(x_320);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
x_304 = x_322;
goto block_315;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_323 = lean_ctor_get(x_319, 1);
lean_inc(x_323);
lean_dec(x_319);
lean_inc(x_302);
x_324 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_324, 0, x_302);
x_325 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_326 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
x_327 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_318, x_326, x_2, x_323);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
x_304 = x_328;
goto block_315;
}
}
block_315:
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_305 = l_Lean_Meta_instantiateMVars(x_302, x_2, x_304);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = l_Lean_Meta_hasAssignableMVar(x_306, x_2, x_307);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_unbox(x_309);
lean_dec(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_dec(x_308);
if (lean_is_scalar(x_303)) {
 x_312 = lean_alloc_ctor(1, 1, 0);
} else {
 x_312 = x_303;
}
lean_ctor_set(x_312, 0, x_306);
x_233 = x_312;
x_234 = x_311;
goto block_280;
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_306);
lean_dec(x_303);
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
lean_dec(x_308);
x_314 = lean_box(0);
x_233 = x_314;
x_234 = x_313;
goto block_280;
}
}
}
}
else
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_329 = lean_ctor_get(x_298, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_298, 1);
lean_inc(x_330);
lean_dec(x_298);
x_281 = x_329;
x_282 = x_330;
goto block_291;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_347 = lean_ctor_get(x_294, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_294, 1);
lean_inc(x_348);
lean_dec(x_294);
x_281 = x_347;
x_282 = x_348;
goto block_291;
}
block_280:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 3);
lean_inc(x_237);
x_238 = lean_ctor_get(x_234, 4);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 5);
lean_inc(x_239);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 lean_ctor_release(x_234, 4);
 lean_ctor_release(x_234, 5);
 x_240 = x_234;
} else {
 lean_dec_ref(x_234);
 x_240 = lean_box(0);
}
lean_inc(x_238);
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(0, 6, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_235);
lean_ctor_set(x_241, 1, x_62);
lean_ctor_set(x_241, 2, x_236);
lean_ctor_set(x_241, 3, x_237);
lean_ctor_set(x_241, 4, x_238);
lean_ctor_set(x_241, 5, x_239);
if (lean_obj_tag(x_233) == 0)
{
lean_dec(x_238);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = x_233;
x_29 = x_241;
goto block_60;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_268; 
x_242 = lean_ctor_get(x_233, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_243 = x_233;
} else {
 lean_dec_ref(x_233);
 x_243 = lean_box(0);
}
x_268 = lean_ctor_get_uint8(x_238, sizeof(void*)*1);
lean_dec(x_238);
if (x_268 == 0)
{
x_244 = x_241;
goto block_267;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_269 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_270 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_269, x_2, x_241);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_244 = x_273;
goto block_267;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_274 = lean_ctor_get(x_270, 1);
lean_inc(x_274);
lean_dec(x_270);
lean_inc(x_242);
x_275 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_275, 0, x_242);
x_276 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_277 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_269, x_277, x_2, x_274);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_244 = x_279;
goto block_267;
}
}
block_267:
{
lean_object* x_245; 
lean_inc(x_2);
lean_inc(x_242);
x_245 = l_Lean_Meta_inferType(x_242, x_2, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_5);
lean_ctor_set(x_248, 1, x_6);
lean_ctor_set(x_248, 2, x_7);
lean_ctor_set(x_248, 3, x_8);
lean_ctor_set(x_248, 4, x_9);
lean_inc(x_25);
x_249 = l_Lean_Meta_isExprDefEq(x_25, x_246, x_248, x_247);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_unbox(x_250);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_2);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec(x_249);
x_253 = lean_box(0);
x_28 = x_253;
x_29 = x_252;
goto block_60;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
lean_dec(x_249);
x_255 = l_Lean_Meta_instantiateMVars(x_242, x_2, x_254);
lean_dec(x_2);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
if (lean_is_scalar(x_243)) {
 x_258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_258 = x_243;
}
lean_ctor_set(x_258, 0, x_256);
x_28 = x_258;
x_29 = x_257;
goto block_60;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
x_259 = lean_ctor_get(x_249, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_249, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_261 = x_249;
} else {
 lean_dec_ref(x_249);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_263 = lean_ctor_get(x_245, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_245, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_265 = x_245;
} else {
 lean_dec_ref(x_245);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
}
block_291:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 2);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 3);
lean_inc(x_285);
x_286 = lean_ctor_get(x_282, 4);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 5);
lean_inc(x_287);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 lean_ctor_release(x_282, 2);
 lean_ctor_release(x_282, 3);
 lean_ctor_release(x_282, 4);
 lean_ctor_release(x_282, 5);
 x_288 = x_282;
} else {
 lean_dec_ref(x_282);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 6, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_283);
lean_ctor_set(x_289, 1, x_62);
lean_ctor_set(x_289, 2, x_284);
lean_ctor_set(x_289, 3, x_285);
lean_ctor_set(x_289, 4, x_286);
lean_ctor_set(x_289, 5, x_287);
if (lean_is_scalar(x_22)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_22;
 lean_ctor_set_tag(x_290, 1);
}
lean_ctor_set(x_290, 0, x_281);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_349 = lean_ctor_get(x_68, 0);
lean_inc(x_349);
lean_dec(x_68);
if (lean_is_scalar(x_22)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_22;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_26);
return x_350;
}
block_60:
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_28);
x_35 = l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_34, x_25, x_28);
lean_ctor_set(x_32, 2, x_35);
if (lean_is_scalar(x_27)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_27;
}
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
x_39 = lean_ctor_get(x_32, 2);
x_40 = lean_ctor_get(x_32, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
lean_inc(x_28);
x_41 = l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_39, x_25, x_28);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_29, 2, x_42);
if (lean_is_scalar(x_27)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_27;
}
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_29);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = lean_ctor_get(x_29, 2);
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
x_47 = lean_ctor_get(x_29, 3);
x_48 = lean_ctor_get(x_29, 4);
x_49 = lean_ctor_get(x_29, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_44);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_44, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_44, 3);
lean_inc(x_53);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_54 = x_44;
} else {
 lean_dec_ref(x_44);
 x_54 = lean_box(0);
}
lean_inc(x_28);
x_55 = l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_52, x_25, x_28);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 4, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_53);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_49);
if (lean_is_scalar(x_27)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_27;
}
lean_ctor_set(x_58, 0, x_28);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_25);
if (lean_is_scalar(x_27)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_27;
}
lean_ctor_set(x_59, 0, x_28);
lean_ctor_set(x_59, 1, x_29);
return x_59;
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_351 = !lean_is_exclusive(x_24);
if (x_351 == 0)
{
return x_24;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_24, 0);
x_353 = lean_ctor_get(x_24, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_24);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; uint8_t x_362; uint8_t x_363; uint8_t x_364; lean_object* x_365; uint8_t x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_355 = lean_ctor_get(x_2, 0);
x_356 = lean_ctor_get(x_2, 1);
x_357 = lean_ctor_get(x_2, 2);
x_358 = lean_ctor_get(x_2, 3);
x_359 = lean_ctor_get(x_2, 4);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_2);
x_360 = lean_ctor_get(x_355, 0);
lean_inc(x_360);
x_361 = lean_ctor_get_uint8(x_355, sizeof(void*)*1 + 2);
x_362 = lean_ctor_get_uint8(x_355, sizeof(void*)*1 + 3);
x_363 = lean_ctor_get_uint8(x_355, sizeof(void*)*1 + 4);
x_364 = lean_ctor_get_uint8(x_355, sizeof(void*)*1 + 5);
x_365 = l___private_Lean_Meta_SynthInstance_6__getMaxSteps(x_360);
x_366 = 1;
x_367 = 2;
x_368 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_368, 0, x_360);
lean_ctor_set_uint8(x_368, sizeof(void*)*1, x_366);
lean_ctor_set_uint8(x_368, sizeof(void*)*1 + 1, x_366);
lean_ctor_set_uint8(x_368, sizeof(void*)*1 + 2, x_361);
lean_ctor_set_uint8(x_368, sizeof(void*)*1 + 3, x_362);
lean_ctor_set_uint8(x_368, sizeof(void*)*1 + 4, x_363);
lean_ctor_set_uint8(x_368, sizeof(void*)*1 + 5, x_364);
lean_ctor_set_uint8(x_368, sizeof(void*)*1 + 6, x_367);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
x_369 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_356);
lean_ctor_set(x_369, 2, x_357);
lean_ctor_set(x_369, 3, x_358);
lean_ctor_set(x_369, 4, x_359);
x_370 = l_Lean_Meta_instantiateMVars(x_1, x_369, x_3);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
x_374 = l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1;
lean_inc(x_369);
x_375 = l_Lean_Meta_forallTelescopeReducing___rarg(x_371, x_374, x_369, x_372);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
x_400 = lean_ctor_get(x_377, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
x_403 = lean_ctor_get(x_377, 3);
lean_inc(x_403);
x_404 = lean_ctor_get(x_377, 4);
lean_inc(x_404);
x_405 = lean_ctor_get(x_377, 5);
lean_inc(x_405);
x_406 = lean_ctor_get(x_402, 2);
lean_inc(x_406);
x_407 = l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_406, x_376);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_457; lean_object* x_458; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 lean_ctor_release(x_377, 4);
 lean_ctor_release(x_377, 5);
 x_408 = x_377;
} else {
 lean_dec_ref(x_377);
 x_408 = lean_box(0);
}
lean_inc(x_401);
x_468 = l_Lean_MetavarContext_incDepth(x_401);
if (lean_is_scalar(x_408)) {
 x_469 = lean_alloc_ctor(0, 6, 0);
} else {
 x_469 = x_408;
}
lean_ctor_set(x_469, 0, x_400);
lean_ctor_set(x_469, 1, x_468);
lean_ctor_set(x_469, 2, x_402);
lean_ctor_set(x_469, 3, x_403);
lean_ctor_set(x_469, 4, x_404);
lean_ctor_set(x_469, 5, x_405);
lean_inc(x_369);
lean_inc(x_376);
x_470 = l___private_Lean_Meta_SynthInstance_5__preprocessOutParam(x_376, x_369, x_469);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_508; uint8_t x_509; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_508 = lean_ctor_get(x_472, 4);
lean_inc(x_508);
x_509 = lean_ctor_get_uint8(x_508, sizeof(void*)*1);
lean_dec(x_508);
if (x_509 == 0)
{
x_473 = x_472;
goto block_507;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; 
x_510 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_511 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_510, x_369, x_472);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_unbox(x_512);
lean_dec(x_512);
if (x_513 == 0)
{
lean_object* x_514; 
x_514 = lean_ctor_get(x_511, 1);
lean_inc(x_514);
lean_dec(x_511);
x_473 = x_514;
goto block_507;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_515 = lean_ctor_get(x_511, 1);
lean_inc(x_515);
lean_dec(x_511);
lean_inc(x_376);
x_516 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_516, 0, x_376);
x_517 = l_Lean_Meta_synthInstance_x3f___closed__9;
x_518 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
lean_inc(x_471);
x_519 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_519, 0, x_471);
x_520 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
x_521 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_510, x_520, x_369, x_515);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
lean_dec(x_521);
x_473 = x_522;
goto block_507;
}
}
block_507:
{
lean_object* x_474; 
lean_inc(x_369);
x_474 = l_Lean_Meta_SynthInstance_main(x_471, x_365, x_369, x_473);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; 
lean_dec(x_373);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; 
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
x_409 = x_475;
x_410 = x_476;
goto block_456;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_492; uint8_t x_493; 
x_477 = lean_ctor_get(x_474, 1);
lean_inc(x_477);
lean_dec(x_474);
x_478 = lean_ctor_get(x_475, 0);
lean_inc(x_478);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 x_479 = x_475;
} else {
 lean_dec_ref(x_475);
 x_479 = lean_box(0);
}
x_492 = lean_ctor_get(x_477, 4);
lean_inc(x_492);
x_493 = lean_ctor_get_uint8(x_492, sizeof(void*)*1);
lean_dec(x_492);
if (x_493 == 0)
{
x_480 = x_477;
goto block_491;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_494 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_495 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_494, x_369, x_477);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_unbox(x_496);
lean_dec(x_496);
if (x_497 == 0)
{
lean_object* x_498; 
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
x_480 = x_498;
goto block_491;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_499 = lean_ctor_get(x_495, 1);
lean_inc(x_499);
lean_dec(x_495);
lean_inc(x_478);
x_500 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_500, 0, x_478);
x_501 = l_Lean_Meta_synthInstance_x3f___closed__6;
x_502 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_500);
x_503 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_494, x_502, x_369, x_499);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
lean_dec(x_503);
x_480 = x_504;
goto block_491;
}
}
block_491:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_481 = l_Lean_Meta_instantiateMVars(x_478, x_369, x_480);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = l_Lean_Meta_hasAssignableMVar(x_482, x_369, x_483);
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_unbox(x_485);
lean_dec(x_485);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_484, 1);
lean_inc(x_487);
lean_dec(x_484);
if (lean_is_scalar(x_479)) {
 x_488 = lean_alloc_ctor(1, 1, 0);
} else {
 x_488 = x_479;
}
lean_ctor_set(x_488, 0, x_482);
x_409 = x_488;
x_410 = x_487;
goto block_456;
}
else
{
lean_object* x_489; lean_object* x_490; 
lean_dec(x_482);
lean_dec(x_479);
x_489 = lean_ctor_get(x_484, 1);
lean_inc(x_489);
lean_dec(x_484);
x_490 = lean_box(0);
x_409 = x_490;
x_410 = x_489;
goto block_456;
}
}
}
}
else
{
lean_object* x_505; lean_object* x_506; 
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_369);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
x_505 = lean_ctor_get(x_474, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_474, 1);
lean_inc(x_506);
lean_dec(x_474);
x_457 = x_505;
x_458 = x_506;
goto block_467;
}
}
}
else
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_369);
lean_dec(x_365);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
x_523 = lean_ctor_get(x_470, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_470, 1);
lean_inc(x_524);
lean_dec(x_470);
x_457 = x_523;
x_458 = x_524;
goto block_467;
}
block_456:
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 2);
lean_inc(x_412);
x_413 = lean_ctor_get(x_410, 3);
lean_inc(x_413);
x_414 = lean_ctor_get(x_410, 4);
lean_inc(x_414);
x_415 = lean_ctor_get(x_410, 5);
lean_inc(x_415);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 lean_ctor_release(x_410, 5);
 x_416 = x_410;
} else {
 lean_dec_ref(x_410);
 x_416 = lean_box(0);
}
lean_inc(x_414);
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 6, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_411);
lean_ctor_set(x_417, 1, x_401);
lean_ctor_set(x_417, 2, x_412);
lean_ctor_set(x_417, 3, x_413);
lean_ctor_set(x_417, 4, x_414);
lean_ctor_set(x_417, 5, x_415);
if (lean_obj_tag(x_409) == 0)
{
lean_dec(x_414);
lean_dec(x_369);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
x_379 = x_409;
x_380 = x_417;
goto block_399;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_444; 
x_418 = lean_ctor_get(x_409, 0);
lean_inc(x_418);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_419 = x_409;
} else {
 lean_dec_ref(x_409);
 x_419 = lean_box(0);
}
x_444 = lean_ctor_get_uint8(x_414, sizeof(void*)*1);
lean_dec(x_414);
if (x_444 == 0)
{
x_420 = x_417;
goto block_443;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_445 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_446 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_445, x_369, x_417);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_unbox(x_447);
lean_dec(x_447);
if (x_448 == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_446, 1);
lean_inc(x_449);
lean_dec(x_446);
x_420 = x_449;
goto block_443;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_450 = lean_ctor_get(x_446, 1);
lean_inc(x_450);
lean_dec(x_446);
lean_inc(x_418);
x_451 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_451, 0, x_418);
x_452 = l_Lean_Meta_synthInstance_x3f___closed__3;
x_453 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_451);
x_454 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_445, x_453, x_369, x_450);
x_455 = lean_ctor_get(x_454, 1);
lean_inc(x_455);
lean_dec(x_454);
x_420 = x_455;
goto block_443;
}
}
block_443:
{
lean_object* x_421; 
lean_inc(x_369);
lean_inc(x_418);
x_421 = l_Lean_Meta_inferType(x_418, x_369, x_420);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_424, 0, x_355);
lean_ctor_set(x_424, 1, x_356);
lean_ctor_set(x_424, 2, x_357);
lean_ctor_set(x_424, 3, x_358);
lean_ctor_set(x_424, 4, x_359);
lean_inc(x_376);
x_425 = l_Lean_Meta_isExprDefEq(x_376, x_422, x_424, x_423);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; uint8_t x_427; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_unbox(x_426);
lean_dec(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_369);
x_428 = lean_ctor_get(x_425, 1);
lean_inc(x_428);
lean_dec(x_425);
x_429 = lean_box(0);
x_379 = x_429;
x_380 = x_428;
goto block_399;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_430 = lean_ctor_get(x_425, 1);
lean_inc(x_430);
lean_dec(x_425);
x_431 = l_Lean_Meta_instantiateMVars(x_418, x_369, x_430);
lean_dec(x_369);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
if (lean_is_scalar(x_419)) {
 x_434 = lean_alloc_ctor(1, 1, 0);
} else {
 x_434 = x_419;
}
lean_ctor_set(x_434, 0, x_432);
x_379 = x_434;
x_380 = x_433;
goto block_399;
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_369);
x_435 = lean_ctor_get(x_425, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_425, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_437 = x_425;
} else {
 lean_dec_ref(x_425);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_369);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
x_439 = lean_ctor_get(x_421, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_421, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_441 = x_421;
} else {
 lean_dec_ref(x_421);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
}
}
block_467:
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 2);
lean_inc(x_460);
x_461 = lean_ctor_get(x_458, 3);
lean_inc(x_461);
x_462 = lean_ctor_get(x_458, 4);
lean_inc(x_462);
x_463 = lean_ctor_get(x_458, 5);
lean_inc(x_463);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 lean_ctor_release(x_458, 2);
 lean_ctor_release(x_458, 3);
 lean_ctor_release(x_458, 4);
 lean_ctor_release(x_458, 5);
 x_464 = x_458;
} else {
 lean_dec_ref(x_458);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(0, 6, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_459);
lean_ctor_set(x_465, 1, x_401);
lean_ctor_set(x_465, 2, x_460);
lean_ctor_set(x_465, 3, x_461);
lean_ctor_set(x_465, 4, x_462);
lean_ctor_set(x_465, 5, x_463);
if (lean_is_scalar(x_373)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_373;
 lean_ctor_set_tag(x_466, 1);
}
lean_ctor_set(x_466, 0, x_457);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
else
{
lean_object* x_525; lean_object* x_526; 
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_369);
lean_dec(x_365);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
x_525 = lean_ctor_get(x_407, 0);
lean_inc(x_525);
lean_dec(x_407);
if (lean_is_scalar(x_373)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_373;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_377);
return x_526;
}
block_399:
{
uint8_t x_381; 
x_381 = l_Lean_Expr_hasMVar(x_376);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_382 = lean_ctor_get(x_380, 2);
lean_inc(x_382);
x_383 = lean_ctor_get(x_380, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_380, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_380, 3);
lean_inc(x_385);
x_386 = lean_ctor_get(x_380, 4);
lean_inc(x_386);
x_387 = lean_ctor_get(x_380, 5);
lean_inc(x_387);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 lean_ctor_release(x_380, 2);
 lean_ctor_release(x_380, 3);
 lean_ctor_release(x_380, 4);
 lean_ctor_release(x_380, 5);
 x_388 = x_380;
} else {
 lean_dec_ref(x_380);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_382, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_382, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_382, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_382, 3);
lean_inc(x_392);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 lean_ctor_release(x_382, 2);
 lean_ctor_release(x_382, 3);
 x_393 = x_382;
} else {
 lean_dec_ref(x_382);
 x_393 = lean_box(0);
}
lean_inc(x_379);
x_394 = l_PersistentHashMap_insert___at_Lean_Meta_synthInstance_x3f___spec__1(x_391, x_376, x_379);
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(0, 4, 0);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_389);
lean_ctor_set(x_395, 1, x_390);
lean_ctor_set(x_395, 2, x_394);
lean_ctor_set(x_395, 3, x_392);
if (lean_is_scalar(x_388)) {
 x_396 = lean_alloc_ctor(0, 6, 0);
} else {
 x_396 = x_388;
}
lean_ctor_set(x_396, 0, x_383);
lean_ctor_set(x_396, 1, x_384);
lean_ctor_set(x_396, 2, x_395);
lean_ctor_set(x_396, 3, x_385);
lean_ctor_set(x_396, 4, x_386);
lean_ctor_set(x_396, 5, x_387);
if (lean_is_scalar(x_378)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_378;
}
lean_ctor_set(x_397, 0, x_379);
lean_ctor_set(x_397, 1, x_396);
return x_397;
}
else
{
lean_object* x_398; 
lean_dec(x_376);
if (lean_is_scalar(x_378)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_378;
}
lean_ctor_set(x_398, 0, x_379);
lean_ctor_set(x_398, 1, x_380);
return x_398;
}
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_373);
lean_dec(x_369);
lean_dec(x_365);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
x_527 = lean_ctor_get(x_375, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_375, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_529 = x_375;
} else {
 lean_dec_ref(x_375);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_Meta_synthInstance_x3f___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_Meta_synthInstance_x3f___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Meta_synthInstance_x3f___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Meta_synthInstance_x3f___spec__6(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Meta_synthInstance_x3f___spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_trySynthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 4, x_7);
x_8 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Option_toLOption___rarg(x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Option_toLOption___rarg(x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
switch (lean_obj_tag(x_16)) {
case 11:
{
uint8_t x_17; 
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = lean_box(2);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_box(2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
case 12:
{
uint8_t x_23; 
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 0);
lean_dec(x_24);
x_25 = lean_box(2);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_8, 0);
lean_dec(x_30);
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
x_39 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
lean_inc(x_33);
lean_dec(x_5);
x_40 = 1;
x_41 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_34);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 1, x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 2, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 3, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 4, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 5, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 6, x_39);
lean_ctor_set(x_2, 0, x_41);
x_42 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = l_Option_toLOption___rarg(x_43);
lean_dec(x_43);
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
lean_object* x_48; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
switch (lean_obj_tag(x_48)) {
case 11:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
x_51 = lean_box(2);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
 lean_ctor_set_tag(x_52, 0);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
case 12:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
x_55 = lean_box(2);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
 lean_ctor_set_tag(x_56, 0);
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_58 = x_42;
} else {
 lean_dec_ref(x_42);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
x_62 = lean_ctor_get(x_2, 2);
x_63 = lean_ctor_get(x_2, 3);
x_64 = lean_ctor_get(x_2, 4);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_2);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
x_67 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 1);
x_68 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 2);
x_69 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 3);
x_70 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 5);
x_71 = lean_ctor_get_uint8(x_60, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_72 = x_60;
} else {
 lean_dec_ref(x_60);
 x_72 = lean_box(0);
}
x_73 = 1;
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 1, 7);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_66);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 1, x_67);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 2, x_68);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 3, x_69);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 4, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 5, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*1 + 6, x_71);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_61);
lean_ctor_set(x_75, 2, x_62);
lean_ctor_set(x_75, 3, x_63);
lean_ctor_set(x_75, 4, x_64);
x_76 = l_Lean_Meta_synthInstance_x3f(x_1, x_75, x_3);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = l_Option_toLOption___rarg(x_77);
lean_dec(x_77);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
switch (lean_obj_tag(x_82)) {
case 11:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_82);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_84 = x_76;
} else {
 lean_dec_ref(x_76);
 x_84 = lean_box(0);
}
x_85 = lean_box(2);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
 lean_ctor_set_tag(x_86, 0);
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
case 12:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_82);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_88 = x_76;
} else {
 lean_dec_ref(x_76);
 x_88 = lean_box(0);
}
x_89 = lean_box(2);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
 lean_ctor_set_tag(x_90, 0);
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
default: 
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_92 = x_76;
} else {
 lean_dec_ref(x_76);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
}
}
lean_object* l_Lean_Meta_synthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_synthInstance_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
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
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
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
lean_object* l_Lean_Meta_synthPendingImp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Meta_getMVarDecl(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*5);
x_7 = lean_box(x_6);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_9);
x_10 = l_Lean_Meta_isClass(x_9, x_2, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
lean_inc(x_2);
x_21 = l_Lean_Meta_synthInstance_x3f(x_9, x_2, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_21, 1);
x_33 = lean_ctor_get(x_21, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_1);
x_36 = lean_metavar_ctx_is_expr_assigned(x_35, x_1);
if (x_36 == 0)
{
lean_object* x_37; 
lean_free_object(x_21);
x_37 = l_Lean_Meta_assignExprMVar(x_1, x_34, x_2, x_32);
lean_dec(x_2);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = 1;
x_41 = lean_box(x_40);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; lean_object* x_51; 
lean_dec(x_34);
lean_dec(x_2);
lean_dec(x_1);
x_50 = 0;
x_51 = lean_box(x_50);
lean_ctor_set(x_21, 0, x_51);
return x_21;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_dec(x_21);
x_53 = lean_ctor_get(x_22, 0);
lean_inc(x_53);
lean_dec(x_22);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_inc(x_1);
x_55 = lean_metavar_ctx_is_expr_assigned(x_54, x_1);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_Meta_assignExprMVar(x_1, x_53, x_2, x_52);
lean_dec(x_2);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = 1;
x_60 = lean_box(x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_53);
lean_dec(x_2);
lean_dec(x_1);
x_66 = 0;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_52);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_21);
if (x_69 == 0)
{
return x_21;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_21, 0);
x_71 = lean_ctor_get(x_21, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_21);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_10);
if (x_73 == 0)
{
return x_10;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_10, 0);
x_75 = lean_ctor_get(x_10, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_10);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_4);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_4, 0);
lean_dec(x_78);
x_79 = 0;
x_80 = lean_box(x_79);
lean_ctor_set(x_4, 0, x_80);
return x_4;
}
else
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_4, 1);
lean_inc(x_81);
lean_dec(x_4);
x_82 = 0;
x_83 = lean_box(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_4);
if (x_85 == 0)
{
return x_4;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_4, 0);
x_87 = lean_ctor_get(x_4, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_4);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
lean_object* _init_l_Lean_Meta_setSynthPendingRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_synthPendingImp), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_setSynthPendingRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_synthPendingRef;
x_3 = l_Lean_Meta_setSynthPendingRef___closed__1;
x_4 = lean_io_ref_set(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_SynthInstance_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_SynthInstance_newSubgoal___closed__2;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2;
x_12 = l_Lean_registerTraceClass(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_15 = l_Lean_registerTraceClass(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_SynthInstance_generate___closed__2;
x_18 = l_Lean_registerTraceClass(x_17, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
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
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
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
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
return x_6;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
return x_3;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_3);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_Instances(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Meta_AbstractMVars(lean_object*);
lean_object* initialize_Lean_Meta_WHNF(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_SynthInstance(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Instances(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1 = _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__1);
l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2 = _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__2);
l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3 = _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__3);
l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4 = _init_l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr___closed__4);
res = l_Lean_Meta_SynthInstance_mkInferTCGoalsLRAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr);
lean_dec_ref(res);
l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1 = _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_GeneratorNode_inhabited___closed__1);
l_Lean_Meta_SynthInstance_GeneratorNode_inhabited = _init_l_Lean_Meta_SynthInstance_GeneratorNode_inhabited();
lean_mark_persistent(l_Lean_Meta_SynthInstance_GeneratorNode_inhabited);
l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1 = _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_Consumernode_inhabited___closed__1);
l_Lean_Meta_SynthInstance_Consumernode_inhabited = _init_l_Lean_Meta_SynthInstance_Consumernode_inhabited();
lean_mark_persistent(l_Lean_Meta_SynthInstance_Consumernode_inhabited);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__1);
l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2 = _init_l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_MkTableKey_normLevel___main___closed__2);
l_Lean_Meta_SynthInstance_mkTableKey___closed__1 = _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___closed__1);
l_Lean_Meta_SynthInstance_mkTableKey___closed__2 = _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___closed__2);
l_Lean_Meta_SynthInstance_mkTableKey___closed__3 = _init_l_Lean_Meta_SynthInstance_mkTableKey___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_mkTableKey___closed__3);
l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1 = _init_l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_Answer_inhabited___closed__1);
l_Lean_Meta_SynthInstance_Answer_inhabited = _init_l_Lean_Meta_SynthInstance_Answer_inhabited();
lean_mark_persistent(l_Lean_Meta_SynthInstance_Answer_inhabited);
l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1 = _init_l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_SynthM_inhabited___closed__1);
l_Lean_Meta_SynthInstance_tracer___closed__1 = _init_l_Lean_Meta_SynthInstance_tracer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__1);
l_Lean_Meta_SynthInstance_tracer___closed__2 = _init_l_Lean_Meta_SynthInstance_tracer___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__2);
l_Lean_Meta_SynthInstance_tracer___closed__3 = _init_l_Lean_Meta_SynthInstance_tracer___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__3);
l_Lean_Meta_SynthInstance_tracer___closed__4 = _init_l_Lean_Meta_SynthInstance_tracer___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__4);
l_Lean_Meta_SynthInstance_tracer___closed__5 = _init_l_Lean_Meta_SynthInstance_tracer___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer___closed__5);
l_Lean_Meta_SynthInstance_tracer = _init_l_Lean_Meta_SynthInstance_tracer();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tracer);
l_Lean_Meta_SynthInstance_meta2Synth___closed__1 = _init_l_Lean_Meta_SynthInstance_meta2Synth___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_meta2Synth___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__2);
l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_SynthInstance_getInstances___spec__2___closed__3);
l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_getInstances___closed__1 = _init_l_Lean_Meta_SynthInstance_getInstances___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getInstances___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___closed__1 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__1);
l_Lean_Meta_SynthInstance_newSubgoal___closed__2 = _init_l_Lean_Meta_SynthInstance_newSubgoal___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_newSubgoal___closed__2);
l_Lean_Meta_SynthInstance_getEntry___closed__1 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__1);
l_Lean_Meta_SynthInstance_getEntry___closed__2 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__2);
l_Lean_Meta_SynthInstance_getEntry___closed__3 = _init_l_Lean_Meta_SynthInstance_getEntry___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_getEntry___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__1);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__2);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__3);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__4);
l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5 = _init_l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_tryResolveCore___lambda__1___closed__5);
l_Lean_Meta_SynthInstance_wakeUp___closed__1 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__1);
l_Lean_Meta_SynthInstance_wakeUp___closed__2 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__2);
l_Lean_Meta_SynthInstance_wakeUp___closed__3 = _init_l_Lean_Meta_SynthInstance_wakeUp___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_wakeUp___closed__3);
l_Lean_Meta_SynthInstance_addAnswer___closed__1 = _init_l_Lean_Meta_SynthInstance_addAnswer___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___closed__1);
l_Lean_Meta_SynthInstance_addAnswer___closed__2 = _init_l_Lean_Meta_SynthInstance_addAnswer___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_addAnswer___closed__2);
l_Lean_Meta_SynthInstance_generate___closed__1 = _init_l_Lean_Meta_SynthInstance_generate___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__1);
l_Lean_Meta_SynthInstance_generate___closed__2 = _init_l_Lean_Meta_SynthInstance_generate___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__2);
l_Lean_Meta_SynthInstance_generate___closed__3 = _init_l_Lean_Meta_SynthInstance_generate___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__3);
l_Lean_Meta_SynthInstance_generate___closed__4 = _init_l_Lean_Meta_SynthInstance_generate___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__4);
l_Lean_Meta_SynthInstance_generate___closed__5 = _init_l_Lean_Meta_SynthInstance_generate___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_generate___closed__5);
l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1 = _init_l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1();
lean_mark_persistent(l_Array_back___at_Lean_Meta_SynthInstance_getNextToResume___spec__1___closed__1);
l_Lean_Meta_SynthInstance_resume___closed__1 = _init_l_Lean_Meta_SynthInstance_resume___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__1);
l_Lean_Meta_SynthInstance_resume___closed__2 = _init_l_Lean_Meta_SynthInstance_resume___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__2);
l_Lean_Meta_SynthInstance_resume___closed__3 = _init_l_Lean_Meta_SynthInstance_resume___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__3);
l_Lean_Meta_SynthInstance_resume___closed__4 = _init_l_Lean_Meta_SynthInstance_resume___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__4);
l_Lean_Meta_SynthInstance_resume___closed__5 = _init_l_Lean_Meta_SynthInstance_resume___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__5);
l_Lean_Meta_SynthInstance_resume___closed__6 = _init_l_Lean_Meta_SynthInstance_resume___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__6);
l_Lean_Meta_SynthInstance_resume___closed__7 = _init_l_Lean_Meta_SynthInstance_resume___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_resume___closed__7);
l_Lean_Meta_SynthInstance_synth___main___closed__1 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__1);
l_Lean_Meta_SynthInstance_synth___main___closed__2 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__2);
l_Lean_Meta_SynthInstance_synth___main___closed__3 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__3);
l_Lean_Meta_SynthInstance_synth___main___closed__4 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__4);
l_Lean_Meta_SynthInstance_synth___main___closed__5 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__5();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__5);
l_Lean_Meta_SynthInstance_synth___main___closed__6 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__6();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__6);
l_Lean_Meta_SynthInstance_synth___main___closed__7 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__7();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__7);
l_Lean_Meta_SynthInstance_synth___main___closed__8 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__8();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__8);
l_Lean_Meta_SynthInstance_synth___main___closed__9 = _init_l_Lean_Meta_SynthInstance_synth___main___closed__9();
lean_mark_persistent(l_Lean_Meta_SynthInstance_synth___main___closed__9);
l_Lean_Meta_SynthInstance_main___closed__1 = _init_l_Lean_Meta_SynthInstance_main___closed__1();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__1);
l_Lean_Meta_SynthInstance_main___closed__2 = _init_l_Lean_Meta_SynthInstance_main___closed__2();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__2);
l_Lean_Meta_SynthInstance_main___closed__3 = _init_l_Lean_Meta_SynthInstance_main___closed__3();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__3);
l_Lean_Meta_SynthInstance_main___closed__4 = _init_l_Lean_Meta_SynthInstance_main___closed__4();
lean_mark_persistent(l_Lean_Meta_SynthInstance_main___closed__4);
l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1 = _init_l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_2__preprocess___closed__1);
l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1 = _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__1);
l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2 = _init_l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_SynthInstance_4__preprocessArgs___main___closed__2);
l_Lean_Meta_maxStepsOption___closed__1 = _init_l_Lean_Meta_maxStepsOption___closed__1();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__1);
l_Lean_Meta_maxStepsOption___closed__2 = _init_l_Lean_Meta_maxStepsOption___closed__2();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__2);
l_Lean_Meta_maxStepsOption___closed__3 = _init_l_Lean_Meta_maxStepsOption___closed__3();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__3);
l_Lean_Meta_maxStepsOption___closed__4 = _init_l_Lean_Meta_maxStepsOption___closed__4();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__4);
l_Lean_Meta_maxStepsOption___closed__5 = _init_l_Lean_Meta_maxStepsOption___closed__5();
lean_mark_persistent(l_Lean_Meta_maxStepsOption___closed__5);
res = l_Lean_Meta_maxStepsOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_synthInstance_x3f___closed__1 = _init_l_Lean_Meta_synthInstance_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__1);
l_Lean_Meta_synthInstance_x3f___closed__2 = _init_l_Lean_Meta_synthInstance_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__2);
l_Lean_Meta_synthInstance_x3f___closed__3 = _init_l_Lean_Meta_synthInstance_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__3);
l_Lean_Meta_synthInstance_x3f___closed__4 = _init_l_Lean_Meta_synthInstance_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__4);
l_Lean_Meta_synthInstance_x3f___closed__5 = _init_l_Lean_Meta_synthInstance_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__5);
l_Lean_Meta_synthInstance_x3f___closed__6 = _init_l_Lean_Meta_synthInstance_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__6);
l_Lean_Meta_synthInstance_x3f___closed__7 = _init_l_Lean_Meta_synthInstance_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__7);
l_Lean_Meta_synthInstance_x3f___closed__8 = _init_l_Lean_Meta_synthInstance_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__8);
l_Lean_Meta_synthInstance_x3f___closed__9 = _init_l_Lean_Meta_synthInstance_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_synthInstance_x3f___closed__9);
l_Lean_Meta_setSynthPendingRef___closed__1 = _init_l_Lean_Meta_setSynthPendingRef___closed__1();
lean_mark_persistent(l_Lean_Meta_setSynthPendingRef___closed__1);
res = l_Lean_Meta_setSynthPendingRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_SynthInstance_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

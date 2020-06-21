// Lean compiler output
// Module: Lean.Meta.Tactic.Cases
// Imports: Lean.Meta.AppBuilder Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Injection Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Subst
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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__7;
lean_object* l_Lean_Meta_getLCtx___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9;
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__7;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__3;
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs(lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__5;
lean_object* l___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_casesOnSuffix;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_6__visit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkNoConfusion___closed__4;
lean_object* l_Lean_Meta_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__1;
extern lean_object* l_Lean_Meta_mkHEqRefl___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1;
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___closed__1;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__8;
extern lean_object* l_HashSet_Inhabited___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkEqRefl___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7;
extern lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__4;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_compose(lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_10__regTraceClasses___closed__2;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__mkEqAndProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_inferType(x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_6);
x_11 = l_Lean_Meta_getLevel(x_6, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_6);
x_14 = l_Lean_Meta_isExprDefEq(x_6, x_9, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_20);
x_22 = l_Lean_mkConst(x_21, x_20);
lean_inc(x_1);
lean_inc(x_6);
x_23 = l_Lean_mkApp4(x_22, x_6, x_1, x_9, x_2);
x_24 = l_Lean_Meta_mkHEqRefl___closed__1;
x_25 = l_Lean_mkConst(x_24, x_20);
x_26 = l_Lean_mkAppB(x_25, x_6, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_30);
x_32 = l_Lean_mkConst(x_31, x_30);
lean_inc(x_1);
lean_inc(x_6);
x_33 = l_Lean_mkApp4(x_32, x_6, x_1, x_9, x_2);
x_34 = l_Lean_Meta_mkHEqRefl___closed__1;
x_35 = l_Lean_mkConst(x_34, x_30);
x_36 = l_Lean_mkAppB(x_35, x_6, x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_14, 0);
lean_dec(x_40);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_42);
x_44 = l_Lean_mkConst(x_43, x_42);
lean_inc(x_1);
lean_inc(x_6);
x_45 = l_Lean_mkApp3(x_44, x_6, x_1, x_2);
x_46 = l_Lean_Meta_mkEqRefl___closed__2;
x_47 = l_Lean_mkConst(x_46, x_42);
x_48 = l_Lean_mkAppB(x_47, x_6, x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_14, 0, x_49);
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_dec(x_14);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_52);
x_54 = l_Lean_mkConst(x_53, x_52);
lean_inc(x_1);
lean_inc(x_6);
x_55 = l_Lean_mkApp3(x_54, x_6, x_1, x_2);
x_56 = l_Lean_Meta_mkEqRefl___closed__2;
x_57 = l_Lean_mkConst(x_56, x_52);
x_58 = l_Lean_mkAppB(x_57, x_6, x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_14);
if (x_61 == 0)
{
return x_14;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_11);
if (x_65 == 0)
{
return x_11;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_11, 0);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_11);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_8, 0);
x_71 = lean_ctor_get(x_8, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_8);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
return x_5;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get(x_5, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_5);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = lean_array_push(x_2, x_8);
x_14 = lean_array_push(x_3, x_4);
x_15 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(x_5, x_6, x_7, x_12, x_13, x_14, x_9, x_10);
return x_15;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_apply_4(x_3, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_Inhabited;
x_13 = lean_array_get(x_12, x_1, x_4);
x_14 = lean_array_get(x_12, x_2, x_4);
lean_inc(x_7);
x_15 = l___private_Lean_Meta_Tactic_Cases_1__mkEqAndProof(x_13, x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_5);
lean_closure_set(x_20, 2, x_6);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_1);
lean_closure_set(x_20, 5, x_2);
lean_closure_set(x_20, 6, x_3);
x_21 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2;
x_22 = 0;
x_23 = l_Lean_Meta_withLocalDecl___rarg(x_21, x_18, x_22, x_20, x_7, x_17);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(x_1, x_2, x_3, x_6, x_7, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_1, x_10);
lean_inc(x_2);
x_14 = l_Lean_Meta_getMVarType(x_2, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Lean_Meta_getMVarTag(x_2, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_13);
x_20 = l_Lean_Meta_mkForall(x_13, x_15, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_mkOptionalNode___closed__2;
x_24 = lean_array_push(x_23, x_3);
lean_inc(x_11);
x_25 = l_Lean_Meta_mkForall(x_24, x_21, x_11, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_4);
x_28 = l_Lean_Meta_mkForall(x_4, x_26, x_11, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 2;
x_32 = l_Lean_Meta_mkFreshExprMVarAt(x_5, x_6, x_29, x_18, x_31, x_11, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_33);
x_36 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_7, x_7, x_35, x_33);
x_37 = l_Lean_mkApp(x_36, x_8);
x_38 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_9, x_9, x_35, x_37);
x_39 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
x_40 = lean_array_get_size(x_4);
lean_dec(x_4);
x_41 = lean_box(0);
x_42 = l_Lean_Meta_assignExprMVar(x_2, x_38, x_11, x_34);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = 0;
x_45 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_44, x_39, x_40, x_41, x_11, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_Meta_intro1(x_49, x_44, x_11, x_47);
lean_dec(x_11);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_array_get_size(x_13);
lean_dec(x_13);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_50, 0, x_56);
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_array_get_size(x_13);
lean_dec(x_13);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_48);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_48);
lean_dec(x_13);
x_64 = !lean_is_exclusive(x_50);
if (x_64 == 0)
{
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_50, 0);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_50);
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
lean_dec(x_13);
lean_dec(x_11);
x_68 = !lean_is_exclusive(x_45);
if (x_68 == 0)
{
return x_45;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_45, 0);
x_70 = lean_ctor_get(x_45, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_45);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_11);
x_72 = !lean_is_exclusive(x_42);
if (x_72 == 0)
{
return x_42;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_42, 0);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_42);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_28);
if (x_76 == 0)
{
return x_28;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_28, 0);
x_78 = lean_ctor_get(x_28, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_28);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_25);
if (x_80 == 0)
{
return x_25;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_25, 0);
x_82 = lean_ctor_get(x_25, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_25);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_20);
if (x_84 == 0)
{
return x_20;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_20, 0);
x_86 = lean_ctor_get(x_20, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_20);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_17);
if (x_88 == 0)
{
return x_17;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_17, 0);
x_90 = lean_ctor_get(x_17, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_17);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_14);
if (x_92 == 0)
{
return x_14;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_14, 0);
x_94 = lean_ctor_get(x_14, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_14);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_LocalDecl_toExpr(x_1);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_12);
x_13 = l___private_Lean_Meta_Tactic_Cases_1__mkEqAndProof(x_12, x_2, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_array_push(x_9, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed), 12, 9);
lean_closure_set(x_19, 0, x_8);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_7);
lean_closure_set(x_19, 7, x_12);
lean_closure_set(x_19, 8, x_18);
x_20 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2;
x_21 = 0;
x_22 = l_Lean_Meta_withLocalDecl___rarg(x_20, x_16, x_21, x_19, x_10, x_15);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed), 11, 7);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_6);
x_11 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs___rarg(x_6, x_3, x_10, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_7, x_7, x_11, x_1);
x_13 = l_Lean_LocalDecl_userName(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3), 9, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
x_15 = 0;
x_16 = l_Lean_Meta_withLocalDecl___rarg(x_13, x_12, x_15, x_14, x_9, x_10);
return x_16;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("indexed inductive type expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed inductive datatype");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_7)) {
case 4:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_environment_find(x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
x_15 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_14, x_10, x_11);
lean_dec(x_10);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
x_21 = lean_array_get_size(x_8);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_nat_add(x_18, x_22);
x_24 = lean_nat_dec_eq(x_21, x_23);
lean_dec(x_23);
x_25 = lean_nat_sub(x_21, x_18);
lean_dec(x_18);
x_26 = l_Array_extract___rarg(x_8, x_25, x_21);
lean_dec(x_21);
x_27 = l_Array_extract___rarg(x_8, x_19, x_22);
lean_dec(x_22);
lean_dec(x_8);
x_28 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_19, x_7);
lean_dec(x_27);
if (x_24 == 0)
{
uint8_t x_54; 
x_54 = 0;
x_29 = x_54;
goto block_53;
}
else
{
uint8_t x_55; 
x_55 = 1;
x_29 = x_55;
goto block_53;
}
block_53:
{
lean_object* x_30; 
if (x_20 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_41 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_41, x_10, x_11);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
if (x_29 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_47 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__8;
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_47, x_10, x_11);
lean_dec(x_10);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_dec(x_5);
x_30 = x_11;
goto block_40;
}
}
block_40:
{
lean_object* x_31; 
lean_inc(x_10);
lean_inc(x_28);
x_31 = l_Lean_Meta_inferType(x_28, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed), 10, 6);
lean_closure_set(x_34, 0, x_28);
lean_closure_set(x_34, 1, x_6);
lean_closure_set(x_34, 2, x_1);
lean_closure_set(x_34, 3, x_2);
lean_closure_set(x_34, 4, x_3);
lean_closure_set(x_34, 5, x_26);
x_35 = l_Lean_Meta_forallTelescopeReducing___rarg(x_32, x_34, x_10, x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_56 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
x_57 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_56, x_10, x_11);
lean_dec(x_10);
return x_57;
}
}
}
case 5:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_7, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_dec(x_7);
x_60 = lean_array_set(x_8, x_9, x_59);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_9, x_61);
lean_dec(x_9);
x_7 = x_58;
x_8 = x_60;
x_9 = x_62;
goto _start;
}
default: 
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
x_65 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_64, x_10, x_11);
lean_dec(x_10);
return x_65;
}
}
}
}
lean_object* _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("generalizeIndices");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Meta_checkNotAssigned(x_1, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
x_11 = l_Lean_Meta_getLocalDecl(x_2, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
lean_inc(x_4);
x_15 = l_Lean_Meta_whnf(x_14, x_4, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Expr_getAppNumArgsAux___main(x_16, x_18);
x_20 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
x_24 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(x_1, x_3, x_6, x_7, x_8, x_12, x_16, x_21, x_23, x_4, x_17);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* _init_l_Lean_Meta_generalizeIndices___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getLCtx___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_generalizeIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lambda__1), 5, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Meta_generalizeIndices___closed__1;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Meta_withLocalContext___rarg(x_11, x_12, x_7, x_3, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_generalizeIndices(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 4:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_1);
x_9 = lean_environment_find(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_get_size(x_4);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_16);
x_18 = lean_nat_dec_eq(x_14, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_casesOnSuffix___closed__1;
x_24 = lean_name_mk_string(x_22, x_23);
x_25 = lean_environment_find(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_13, 4);
lean_inc(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_List_lengthAux___main___rarg(x_31, x_32);
lean_dec(x_31);
x_34 = lean_nat_sub(x_14, x_15);
lean_dec(x_15);
x_35 = l_Array_extract___rarg(x_4, x_34, x_14);
lean_dec(x_14);
x_36 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_2);
lean_ctor_set(x_36, 4, x_3);
lean_ctor_set(x_36, 5, x_4);
lean_ctor_set(x_36, 6, x_35);
lean_ctor_set(x_25, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_25);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
return x_39;
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_40);
lean_dec(x_25);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_13, 4);
lean_inc(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_List_lengthAux___main___rarg(x_42, x_43);
lean_dec(x_42);
x_45 = lean_nat_sub(x_14, x_15);
lean_dec(x_15);
x_46 = l_Array_extract___rarg(x_4, x_45, x_14);
lean_dec(x_14);
x_47 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_2);
lean_ctor_set(x_47, 4, x_3);
lean_ctor_set(x_47, 5, x_4);
lean_ctor_set(x_47, 6, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_7);
return x_51;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
}
}
case 5:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 1);
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_array_set(x_4, x_5, x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_5, x_57);
lean_dec(x_5);
x_3 = x_54;
x_4 = x_56;
x_5 = x_58;
goto _start;
}
default: 
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_4);
x_6 = l_Lean_Environment_contains(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_4);
x_10 = l_Lean_Environment_contains(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_2);
x_13 = l_Lean_Meta_getLocalDecl(x_1, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_type(x_14);
lean_inc(x_2);
x_17 = l_Lean_Meta_whnf(x_16, x_2, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_20);
x_22 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
x_26 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1(x_4, x_14, x_18, x_23, x_25, x_2, x_19);
lean_dec(x_2);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
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
lean_dec(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_Expr_isFVar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
}
}
}
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_10 = l_Lean_Expr_Inhabited;
x_11 = lean_array_get(x_10, x_1, x_2);
x_12 = lean_array_get(x_10, x_1, x_9);
lean_dec(x_9);
x_13 = lean_expr_eqv(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = 0;
return x_16;
}
}
}
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
lean_inc(x_8);
x_9 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2(x_1, x_8, x_8, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_7);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = 1;
return x_14;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_fget(x_6, x_8);
lean_inc(x_4);
x_12 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_8 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
return x_12;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_array_fget(x_6, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_LocalDecl_fvarId(x_15);
x_17 = lean_ctor_get(x_1, 3);
x_18 = l_Lean_LocalDecl_fvarId(x_17);
x_19 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(x_1, x_16, x_2, x_3, x_20);
lean_dec(x_16);
if (x_21 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 3);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Expr_hasFVar(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasMVar(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_4);
x_25 = 1;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_27 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_22, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_4);
x_30 = 1;
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_8 = x_32;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_35 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_22, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_4);
x_38 = 1;
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_8, x_39);
lean_dec(x_8);
x_8 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_67; 
x_42 = lean_ctor_get(x_15, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_15, 4);
lean_inc(x_43);
lean_dec(x_15);
x_67 = l_Lean_Expr_hasFVar(x_42);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Expr_hasMVar(x_42);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; 
lean_dec(x_42);
x_69 = 0;
x_70 = l_HashSet_Inhabited___closed__1;
x_44 = x_69;
x_45 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = l_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_42, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_44 = x_75;
x_45 = x_74;
goto block_66;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = l_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_77 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_42, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_44 = x_80;
x_45 = x_79;
goto block_66;
}
block_66:
{
if (x_44 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_hasFVar(x_43);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasMVar(x_43);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_4);
x_48 = 1;
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_43, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_4);
x_52 = 1;
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_8, x_53);
lean_dec(x_8);
x_8 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_4);
x_56 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_43, x_45);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_4);
x_59 = 1;
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_8, x_60);
lean_dec(x_8);
x_8 = x_61;
goto _start;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_43);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_8, x_63);
lean_dec(x_8);
x_8 = x_64;
goto _start;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_15);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_8, x_81);
lean_dec(x_8);
x_8 = x_82;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_16);
lean_dec(x_15);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_8, x_84);
lean_dec(x_8);
x_8 = x_85;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44(x_1, x_2, x_3, x_4, x_6, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_10, x_10, x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_array_fget(x_6, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_LocalDecl_fvarId(x_15);
x_17 = lean_ctor_get(x_1, 3);
x_18 = l_Lean_LocalDecl_fvarId(x_17);
x_19 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(x_1, x_16, x_2, x_3, x_20);
lean_dec(x_16);
if (x_21 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 3);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Expr_hasFVar(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasMVar(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_4);
x_25 = 1;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_27 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_22, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_4);
x_30 = 1;
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_8 = x_32;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_35 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_22, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_4);
x_38 = 1;
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_8, x_39);
lean_dec(x_8);
x_8 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_67; 
x_42 = lean_ctor_get(x_15, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_15, 4);
lean_inc(x_43);
lean_dec(x_15);
x_67 = l_Lean_Expr_hasFVar(x_42);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Expr_hasMVar(x_42);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; 
lean_dec(x_42);
x_69 = 0;
x_70 = l_HashSet_Inhabited___closed__1;
x_44 = x_69;
x_45 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = l_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_42, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_44 = x_75;
x_45 = x_74;
goto block_66;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = l_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_77 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_42, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_44 = x_80;
x_45 = x_79;
goto block_66;
}
block_66:
{
if (x_44 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_hasFVar(x_43);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasMVar(x_43);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_4);
x_48 = 1;
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_43, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_4);
x_52 = 1;
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_8, x_53);
lean_dec(x_8);
x_8 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_4);
x_56 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_43, x_45);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_4);
x_59 = 1;
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_8, x_60);
lean_dec(x_8);
x_8 = x_61;
goto _start;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_43);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_8, x_63);
lean_dec(x_8);
x_8 = x_64;
goto _start;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_15);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_8, x_81);
lean_dec(x_8);
x_8 = x_82;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_16);
lean_dec(x_15);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_8, x_84);
lean_dec(x_8);
x_8 = x_85;
goto _start;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_4);
x_7 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10);
lean_dec(x_9);
return x_11;
}
else
{
lean_dec(x_4);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 6);
x_5 = l_Array_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1(x_1, x_4, x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_6);
x_9 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3(x_4, x_6, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
x_13 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42(x_1, x_4, x_6, x_11, x_12);
lean_dec(x_6);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
lean_object* l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = l_Lean_Meta_FVarSubst_get(x_15, x_10);
lean_inc(x_6);
x_17 = l_Lean_Meta_clear(x_13, x_16, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_6);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_4, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_RBNode_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_4, 2, x_24);
lean_ctor_set(x_4, 0, x_22);
x_3 = x_12;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = l_RBNode_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_10, x_15);
lean_dec(x_10);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_28);
x_3 = x_12;
x_4 = x_29;
x_6 = x_27;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_dec(x_6);
x_35 = l_Lean_Meta_restore(x_32, x_33, x_34, x_5, x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_3 = x_12;
x_6 = x_36;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = x_4;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_array_fget(x_4, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_4, x_3, x_12);
x_14 = x_11;
x_15 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1(x_1, x_2, x_12, x_14, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
x_20 = x_16;
x_21 = lean_array_fset(x_13, x_3, x_20);
lean_dec(x_3);
x_3 = x_19;
x_4 = x_21;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = x_2;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2___boxed), 6, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
x_9 = x_8;
x_10 = lean_apply_2(x_9, x_3, x_4);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Name_inhabited;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = x_13;
x_17 = lean_array_fset(x_9, x_2, x_16);
lean_dec(x_2);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = x_1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1(x_2, x_4, x_3);
x_6 = x_5;
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cases");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_LocalDecl_type(x_6);
x_10 = l_Lean_Expr_heq_x3f___closed__2;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity___main(x_9, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_eq_x3f___closed__2;
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Expr_isAppOfArity___main(x_9, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2;
x_17 = l_Lean_Meta_injectionCore___lambda__1___closed__2;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_16, x_1, x_17, x_7, x_8);
lean_dec(x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Expr_appFn_x21(x_9);
x_20 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_21 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_21);
lean_inc(x_20);
x_22 = l_Lean_Meta_isExprDefEq(x_20, x_21, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_7);
x_26 = l_Lean_Meta_whnf(x_20, x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_7);
x_29 = l_Lean_Meta_whnf(x_21, x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
if (lean_obj_tag(x_27) == 1)
{
switch (lean_obj_tag(x_30)) {
case 0:
{
uint8_t x_76; uint8_t x_77; lean_object* x_78; 
lean_dec(x_30);
lean_dec(x_27);
x_76 = 0;
x_77 = 1;
x_78 = l_Lean_Meta_substCore(x_1, x_2, x_76, x_77, x_7, x_31);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_4, 1);
lean_inc(x_83);
x_84 = x_83;
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2(x_81, x_85, x_84);
x_87 = x_86;
x_88 = lean_ctor_get(x_4, 2);
lean_inc(x_88);
lean_dec(x_4);
x_89 = l_Lean_Meta_FVarSubst_compose(x_81, x_88);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_87);
lean_ctor_set(x_90, 2, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_5);
x_92 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_91, x_7, x_80);
lean_dec(x_7);
return x_92;
}
else
{
uint8_t x_93; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_78);
if (x_93 == 0)
{
return x_78;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_78, 0);
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_78);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
case 1:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_27, 0);
lean_inc(x_97);
lean_dec(x_27);
x_98 = lean_ctor_get(x_30, 0);
lean_inc(x_98);
lean_dec(x_30);
lean_inc(x_7);
x_99 = l_Lean_Meta_getLocalDecl(x_97, x_7, x_31);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_7);
x_101 = l_Lean_Meta_getLocalDecl(x_98, x_7, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = 0;
x_104 = 1;
x_105 = l_Lean_Meta_substCore(x_1, x_2, x_103, x_104, x_7, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_ctor_get(x_4, 1);
lean_inc(x_110);
x_111 = x_110;
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3(x_108, x_112, x_111);
x_114 = x_113;
x_115 = lean_ctor_get(x_4, 2);
lean_inc(x_115);
lean_dec(x_4);
x_116 = l_Lean_Meta_FVarSubst_compose(x_108, x_115);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_109);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set(x_117, 2, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_5);
x_119 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_118, x_7, x_107);
lean_dec(x_7);
return x_119;
}
else
{
uint8_t x_120; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_120 = !lean_is_exclusive(x_105);
if (x_120 == 0)
{
return x_105;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_105, 0);
x_122 = lean_ctor_get(x_105, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_105);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_101);
if (x_124 == 0)
{
return x_101;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_101, 0);
x_126 = lean_ctor_get(x_101, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_101);
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
lean_dec(x_98);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_99);
if (x_128 == 0)
{
return x_99;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_99, 0);
x_130 = lean_ctor_get(x_99, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_99);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
case 2:
{
uint8_t x_132; uint8_t x_133; lean_object* x_134; 
lean_dec(x_30);
lean_dec(x_27);
x_132 = 0;
x_133 = 1;
x_134 = l_Lean_Meta_substCore(x_1, x_2, x_132, x_133, x_7, x_31);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_4, 1);
lean_inc(x_139);
x_140 = x_139;
x_141 = lean_unsigned_to_nat(0u);
x_142 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4(x_137, x_141, x_140);
x_143 = x_142;
x_144 = lean_ctor_get(x_4, 2);
lean_inc(x_144);
lean_dec(x_4);
x_145 = l_Lean_Meta_FVarSubst_compose(x_137, x_144);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_138);
lean_ctor_set(x_146, 1, x_143);
lean_ctor_set(x_146, 2, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_5);
x_148 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_147, x_7, x_136);
lean_dec(x_7);
return x_148;
}
else
{
uint8_t x_149; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_134);
if (x_149 == 0)
{
return x_134;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_134, 0);
x_151 = lean_ctor_get(x_134, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_134);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
case 3:
{
uint8_t x_153; uint8_t x_154; lean_object* x_155; 
lean_dec(x_30);
lean_dec(x_27);
x_153 = 0;
x_154 = 1;
x_155 = l_Lean_Meta_substCore(x_1, x_2, x_153, x_154, x_7, x_31);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
x_160 = lean_ctor_get(x_4, 1);
lean_inc(x_160);
x_161 = x_160;
x_162 = lean_unsigned_to_nat(0u);
x_163 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5(x_158, x_162, x_161);
x_164 = x_163;
x_165 = lean_ctor_get(x_4, 2);
lean_inc(x_165);
lean_dec(x_4);
x_166 = l_Lean_Meta_FVarSubst_compose(x_158, x_165);
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_164);
lean_ctor_set(x_167, 2, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_5);
x_169 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_168, x_7, x_157);
lean_dec(x_7);
return x_169;
}
else
{
uint8_t x_170; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_170 = !lean_is_exclusive(x_155);
if (x_170 == 0)
{
return x_155;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_155, 0);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_155);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
case 4:
{
uint8_t x_174; uint8_t x_175; lean_object* x_176; 
lean_dec(x_30);
lean_dec(x_27);
x_174 = 0;
x_175 = 1;
x_176 = l_Lean_Meta_substCore(x_1, x_2, x_174, x_175, x_7, x_31);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_181 = lean_ctor_get(x_4, 1);
lean_inc(x_181);
x_182 = x_181;
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6(x_179, x_183, x_182);
x_185 = x_184;
x_186 = lean_ctor_get(x_4, 2);
lean_inc(x_186);
lean_dec(x_4);
x_187 = l_Lean_Meta_FVarSubst_compose(x_179, x_186);
x_188 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_188, 0, x_180);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_5);
x_190 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_189, x_7, x_178);
lean_dec(x_7);
return x_190;
}
else
{
uint8_t x_191; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_191 = !lean_is_exclusive(x_176);
if (x_191 == 0)
{
return x_176;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_176, 0);
x_193 = lean_ctor_get(x_176, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_176);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
case 5:
{
uint8_t x_195; uint8_t x_196; lean_object* x_197; 
lean_dec(x_30);
lean_dec(x_27);
x_195 = 0;
x_196 = 1;
x_197 = l_Lean_Meta_substCore(x_1, x_2, x_195, x_196, x_7, x_31);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_202 = lean_ctor_get(x_4, 1);
lean_inc(x_202);
x_203 = x_202;
x_204 = lean_unsigned_to_nat(0u);
x_205 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7(x_200, x_204, x_203);
x_206 = x_205;
x_207 = lean_ctor_get(x_4, 2);
lean_inc(x_207);
lean_dec(x_4);
x_208 = l_Lean_Meta_FVarSubst_compose(x_200, x_207);
x_209 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_209, 0, x_201);
lean_ctor_set(x_209, 1, x_206);
lean_ctor_set(x_209, 2, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_5);
x_211 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_210, x_7, x_199);
lean_dec(x_7);
return x_211;
}
else
{
uint8_t x_212; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_212 = !lean_is_exclusive(x_197);
if (x_212 == 0)
{
return x_197;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_197, 0);
x_214 = lean_ctor_get(x_197, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_197);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
case 6:
{
uint8_t x_216; uint8_t x_217; lean_object* x_218; 
lean_dec(x_30);
lean_dec(x_27);
x_216 = 0;
x_217 = 1;
x_218 = l_Lean_Meta_substCore(x_1, x_2, x_216, x_217, x_7, x_31);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_223 = lean_ctor_get(x_4, 1);
lean_inc(x_223);
x_224 = x_223;
x_225 = lean_unsigned_to_nat(0u);
x_226 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8(x_221, x_225, x_224);
x_227 = x_226;
x_228 = lean_ctor_get(x_4, 2);
lean_inc(x_228);
lean_dec(x_4);
x_229 = l_Lean_Meta_FVarSubst_compose(x_221, x_228);
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_222);
lean_ctor_set(x_230, 1, x_227);
lean_ctor_set(x_230, 2, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_5);
x_232 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_231, x_7, x_220);
lean_dec(x_7);
return x_232;
}
else
{
uint8_t x_233; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_233 = !lean_is_exclusive(x_218);
if (x_233 == 0)
{
return x_218;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_218, 0);
x_235 = lean_ctor_get(x_218, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_218);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
case 7:
{
uint8_t x_237; uint8_t x_238; lean_object* x_239; 
lean_dec(x_30);
lean_dec(x_27);
x_237 = 0;
x_238 = 1;
x_239 = l_Lean_Meta_substCore(x_1, x_2, x_237, x_238, x_7, x_31);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_ctor_get(x_4, 1);
lean_inc(x_244);
x_245 = x_244;
x_246 = lean_unsigned_to_nat(0u);
x_247 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9(x_242, x_246, x_245);
x_248 = x_247;
x_249 = lean_ctor_get(x_4, 2);
lean_inc(x_249);
lean_dec(x_4);
x_250 = l_Lean_Meta_FVarSubst_compose(x_242, x_249);
x_251 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set(x_251, 2, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_5);
x_253 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_252, x_7, x_241);
lean_dec(x_7);
return x_253;
}
else
{
uint8_t x_254; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_254 = !lean_is_exclusive(x_239);
if (x_254 == 0)
{
return x_239;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_239, 0);
x_256 = lean_ctor_get(x_239, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_239);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
case 8:
{
uint8_t x_258; uint8_t x_259; lean_object* x_260; 
lean_dec(x_30);
lean_dec(x_27);
x_258 = 0;
x_259 = 1;
x_260 = l_Lean_Meta_substCore(x_1, x_2, x_258, x_259, x_7, x_31);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_265 = lean_ctor_get(x_4, 1);
lean_inc(x_265);
x_266 = x_265;
x_267 = lean_unsigned_to_nat(0u);
x_268 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10(x_263, x_267, x_266);
x_269 = x_268;
x_270 = lean_ctor_get(x_4, 2);
lean_inc(x_270);
lean_dec(x_4);
x_271 = l_Lean_Meta_FVarSubst_compose(x_263, x_270);
x_272 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_272, 0, x_264);
lean_ctor_set(x_272, 1, x_269);
lean_ctor_set(x_272, 2, x_271);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_5);
x_274 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_273, x_7, x_262);
lean_dec(x_7);
return x_274;
}
else
{
uint8_t x_275; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_275 = !lean_is_exclusive(x_260);
if (x_275 == 0)
{
return x_260;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_260, 0);
x_277 = lean_ctor_get(x_260, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_260);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
case 9:
{
uint8_t x_279; uint8_t x_280; lean_object* x_281; 
lean_dec(x_30);
lean_dec(x_27);
x_279 = 0;
x_280 = 1;
x_281 = l_Lean_Meta_substCore(x_1, x_2, x_279, x_280, x_7, x_31);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
x_286 = lean_ctor_get(x_4, 1);
lean_inc(x_286);
x_287 = x_286;
x_288 = lean_unsigned_to_nat(0u);
x_289 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11(x_284, x_288, x_287);
x_290 = x_289;
x_291 = lean_ctor_get(x_4, 2);
lean_inc(x_291);
lean_dec(x_4);
x_292 = l_Lean_Meta_FVarSubst_compose(x_284, x_291);
x_293 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_293, 0, x_285);
lean_ctor_set(x_293, 1, x_290);
lean_ctor_set(x_293, 2, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_5);
x_295 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_294, x_7, x_283);
lean_dec(x_7);
return x_295;
}
else
{
uint8_t x_296; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_296 = !lean_is_exclusive(x_281);
if (x_296 == 0)
{
return x_281;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_281, 0);
x_298 = lean_ctor_get(x_281, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_281);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
case 10:
{
uint8_t x_300; uint8_t x_301; lean_object* x_302; 
lean_dec(x_30);
lean_dec(x_27);
x_300 = 0;
x_301 = 1;
x_302 = l_Lean_Meta_substCore(x_1, x_2, x_300, x_301, x_7, x_31);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec(x_303);
x_307 = lean_ctor_get(x_4, 1);
lean_inc(x_307);
x_308 = x_307;
x_309 = lean_unsigned_to_nat(0u);
x_310 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12(x_305, x_309, x_308);
x_311 = x_310;
x_312 = lean_ctor_get(x_4, 2);
lean_inc(x_312);
lean_dec(x_4);
x_313 = l_Lean_Meta_FVarSubst_compose(x_305, x_312);
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_306);
lean_ctor_set(x_314, 1, x_311);
lean_ctor_set(x_314, 2, x_313);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_5);
x_316 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_315, x_7, x_304);
lean_dec(x_7);
return x_316;
}
else
{
uint8_t x_317; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_317 = !lean_is_exclusive(x_302);
if (x_317 == 0)
{
return x_302;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_302, 0);
x_319 = lean_ctor_get(x_302, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_302);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
}
case 11:
{
uint8_t x_321; uint8_t x_322; lean_object* x_323; 
lean_dec(x_30);
lean_dec(x_27);
x_321 = 0;
x_322 = 1;
x_323 = l_Lean_Meta_substCore(x_1, x_2, x_321, x_322, x_7, x_31);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_ctor_get(x_324, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
lean_dec(x_324);
x_328 = lean_ctor_get(x_4, 1);
lean_inc(x_328);
x_329 = x_328;
x_330 = lean_unsigned_to_nat(0u);
x_331 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13(x_326, x_330, x_329);
x_332 = x_331;
x_333 = lean_ctor_get(x_4, 2);
lean_inc(x_333);
lean_dec(x_4);
x_334 = l_Lean_Meta_FVarSubst_compose(x_326, x_333);
x_335 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_332);
lean_ctor_set(x_335, 2, x_334);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_5);
x_337 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_336, x_7, x_325);
lean_dec(x_7);
return x_337;
}
else
{
uint8_t x_338; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_338 = !lean_is_exclusive(x_323);
if (x_338 == 0)
{
return x_323;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_323, 0);
x_340 = lean_ctor_get(x_323, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_323);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
default: 
{
uint8_t x_342; uint8_t x_343; lean_object* x_344; 
lean_dec(x_30);
lean_dec(x_27);
x_342 = 0;
x_343 = 1;
x_344 = l_Lean_Meta_substCore(x_1, x_2, x_342, x_343, x_7, x_31);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
lean_dec(x_345);
x_349 = lean_ctor_get(x_4, 1);
lean_inc(x_349);
x_350 = x_349;
x_351 = lean_unsigned_to_nat(0u);
x_352 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14(x_347, x_351, x_350);
x_353 = x_352;
x_354 = lean_ctor_get(x_4, 2);
lean_inc(x_354);
lean_dec(x_4);
x_355 = l_Lean_Meta_FVarSubst_compose(x_347, x_354);
x_356 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_356, 0, x_348);
lean_ctor_set(x_356, 1, x_353);
lean_ctor_set(x_356, 2, x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_5);
x_358 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_357, x_7, x_346);
lean_dec(x_7);
return x_358;
}
else
{
uint8_t x_359; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_359 = !lean_is_exclusive(x_344);
if (x_359 == 0)
{
return x_344;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_344, 0);
x_361 = lean_ctor_get(x_344, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_344);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
}
}
else
{
lean_object* x_363; 
lean_dec(x_27);
x_363 = lean_box(0);
x_32 = x_363;
goto block_75;
}
block_75:
{
lean_dec(x_32);
if (lean_obj_tag(x_30) == 1)
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; 
lean_dec(x_30);
x_33 = 0;
x_34 = 1;
x_35 = l_Lean_Meta_substCore(x_1, x_2, x_33, x_34, x_7, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
x_41 = x_40;
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1(x_38, x_42, x_41);
x_44 = x_43;
x_45 = lean_ctor_get(x_4, 2);
lean_inc(x_45);
lean_dec(x_4);
x_46 = l_Lean_Meta_FVarSubst_compose(x_38, x_45);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
x_49 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_48, x_7, x_37);
lean_dec(x_7);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_35, 0);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_35);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_30);
x_54 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_box(0);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_dec(x_55);
x_65 = lean_nat_add(x_3, x_64);
lean_dec(x_64);
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_4, 2);
lean_inc(x_67);
lean_dec(x_4);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_5);
x_70 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_65, x_69, x_7, x_62);
lean_dec(x_7);
lean_dec(x_65);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_54);
if (x_71 == 0)
{
return x_54;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_54, 0);
x_73 = lean_ctor_get(x_54, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_54);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
else
{
uint8_t x_364; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_364 = !lean_is_exclusive(x_29);
if (x_364 == 0)
{
return x_29;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_29, 0);
x_366 = lean_ctor_get(x_29, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_29);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
}
}
else
{
uint8_t x_368; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_368 = !lean_is_exclusive(x_26);
if (x_368 == 0)
{
return x_26;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_26, 0);
x_370 = lean_ctor_get(x_26, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_26);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
else
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_21);
lean_dec(x_20);
x_372 = lean_ctor_get(x_22, 1);
lean_inc(x_372);
lean_dec(x_22);
x_373 = l_Lean_Meta_clear(x_1, x_2, x_7, x_372);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_4, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_4, 2);
lean_inc(x_377);
lean_dec(x_4);
x_378 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_378, 0, x_374);
lean_ctor_set(x_378, 1, x_376);
lean_ctor_set(x_378, 2, x_377);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_5);
x_380 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_379, x_7, x_375);
lean_dec(x_7);
return x_380;
}
else
{
uint8_t x_381; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_381 = !lean_is_exclusive(x_373);
if (x_381 == 0)
{
return x_373;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_373, 0);
x_383 = lean_ctor_get(x_373, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_373);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_385 = !lean_is_exclusive(x_22);
if (x_385 == 0)
{
return x_22;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_22, 0);
x_387 = lean_ctor_get(x_22, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_22);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_389 = l_Lean_Expr_appFn_x21(x_9);
x_390 = l_Lean_Expr_appFn_x21(x_389);
lean_dec(x_389);
x_391 = l_Lean_Expr_appArg_x21(x_390);
lean_dec(x_390);
x_392 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_2);
x_393 = l_Lean_mkFVar(x_2);
lean_inc(x_7);
x_394 = l_Lean_Meta_mkEqOfHEq(x_393, x_7, x_8);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
lean_inc(x_7);
x_397 = l_Lean_Meta_mkEq(x_391, x_392, x_7, x_396);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = l_Lean_LocalDecl_userName(x_6);
x_401 = l_Lean_Meta_assert(x_1, x_400, x_398, x_395, x_7, x_399);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = l_Lean_Meta_clear(x_402, x_2, x_7, x_403);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_unsigned_to_nat(1u);
x_408 = lean_nat_add(x_3, x_407);
x_409 = lean_ctor_get(x_4, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_4, 2);
lean_inc(x_410);
lean_dec(x_4);
x_411 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_411, 0, x_405);
lean_ctor_set(x_411, 1, x_409);
lean_ctor_set(x_411, 2, x_410);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_5);
x_413 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_408, x_412, x_7, x_406);
lean_dec(x_7);
lean_dec(x_408);
return x_413;
}
else
{
uint8_t x_414; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_414 = !lean_is_exclusive(x_404);
if (x_414 == 0)
{
return x_404;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_404, 0);
x_416 = lean_ctor_get(x_404, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_404);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
else
{
uint8_t x_418; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_418 = !lean_is_exclusive(x_401);
if (x_418 == 0)
{
return x_401;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_401, 0);
x_420 = lean_ctor_get(x_401, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_401);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
uint8_t x_422; 
lean_dec(x_395);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_422 = !lean_is_exclusive(x_397);
if (x_422 == 0)
{
return x_397;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_397, 0);
x_424 = lean_ctor_get(x_397, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_397);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_426 = !lean_is_exclusive(x_394);
if (x_426 == 0)
{
return x_394;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_394, 0);
x_428 = lean_ctor_get(x_394, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_394);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_10__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs [");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_37; uint8_t x_38; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_37 = lean_ctor_get(x_4, 4);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_dec(x_37);
if (x_38 == 0)
{
x_12 = x_4;
goto block_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
x_40 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_39, x_3, x_4);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_12 = x_43;
goto block_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_nat_add(x_8, x_7);
x_46 = l_Nat_repr(x_45);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_11);
x_53 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_53, 0, x_11);
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_39, x_54, x_3, x_44);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_12 = x_56;
goto block_36;
}
}
block_36:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = l_Lean_Meta_intro1(x_11, x_13, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_19, 0, x_17);
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___boxed), 8, 5);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_8);
lean_closure_set(x_20, 3, x_9);
lean_closure_set(x_20, 4, x_10);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_getMVarDecl(x_18, x_3, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 4);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_withLocalContext___rarg(x_25, x_26, x_21, x_3, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_21);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_2);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_2);
x_58 = lean_ctor_get(x_4, 4);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_58, sizeof(void*)*1);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
x_62 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_61, x_3, x_4);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_62, 0);
lean_dec(x_66);
lean_ctor_set(x_62, 0, x_57);
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
lean_dec(x_2);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10;
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_61, x_74, x_3, x_70);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_57);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_57);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_1, x_11, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_4 = x_13;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_array_push(x_5, x_19);
x_4 = x_13;
x_5 = x_20;
x_7 = x_18;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not applicable to the given hypothesis");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after generalizeIndices");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__6;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_3);
x_10 = l___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f(x_3, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Cases_cases___lambda__1___closed__3;
x_14 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_13, x_6, x_12);
lean_dec(x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
x_19 = l_List_redLength___main___rarg(x_18);
x_20 = lean_mk_empty_array_with_capacity(x_19);
lean_dec(x_19);
x_21 = l_List_toArrayAux___main___rarg(x_18, x_20);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_casesOnSuffix;
x_25 = lean_name_mk_string(x_23, x_24);
x_26 = l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices(x_16, x_6, x_15);
lean_dec(x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_78; uint8_t x_79; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
x_78 = lean_ctor_get(x_32, 4);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_78, sizeof(void*)*1);
lean_dec(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = 0;
x_35 = x_80;
x_36 = x_32;
goto block_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
x_82 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_81, x_6, x_32);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
x_35 = x_85;
x_36 = x_84;
goto block_77;
}
block_77:
{
if (x_35 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Meta_induction(x_33, x_34, x_25, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_6);
lean_inc(x_31);
x_40 = l___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices(x_31, x_38, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_41, x_21);
lean_dec(x_21);
x_44 = lean_ctor_get(x_31, 3);
lean_inc(x_44);
lean_dec(x_31);
x_45 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(x_44, x_43, x_6, x_42);
lean_dec(x_6);
lean_dec(x_43);
lean_dec(x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
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
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_33);
x_54 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_54, 0, x_33);
x_55 = l_Lean_Meta_Cases_cases___lambda__1___closed__7;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
x_58 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_57, x_56, x_6, x_36);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Meta_induction(x_33, x_34, x_25, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_6);
lean_inc(x_31);
x_63 = l___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices(x_31, x_61, x_6, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_64, x_21);
lean_dec(x_21);
x_67 = lean_ctor_get(x_31, 3);
lean_inc(x_67);
lean_dec(x_31);
x_68 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(x_67, x_66, x_6, x_65);
lean_dec(x_6);
lean_dec(x_66);
lean_dec(x_67);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_6);
x_69 = !lean_is_exclusive(x_63);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
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
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_6);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
return x_60;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_60);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_30);
if (x_86 == 0)
{
return x_30;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_30, 0);
x_88 = lean_ctor_get(x_30, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_30);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_26, 1);
lean_inc(x_90);
lean_dec(x_26);
x_91 = l_Lean_Meta_induction(x_1, x_3, x_25, x_4, x_5, x_6, x_90);
lean_dec(x_6);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_93, x_21);
lean_dec(x_21);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_91);
x_97 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_95, x_21);
lean_dec(x_21);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_21);
x_99 = !lean_is_exclusive(x_91);
if (x_99 == 0)
{
return x_91;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_91, 0);
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_91);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_10);
if (x_103 == 0)
{
return x_10;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_10, 0);
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_10);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_8);
if (x_107 == 0)
{
return x_8;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_8, 0);
x_109 = lean_ctor_get(x_8, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_8);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2;
x_8 = lean_box(x_4);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lambda__1___boxed), 7, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_8);
x_10 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 4);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_withLocalContext___rarg(x_13, x_14, x_9, x_5, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Meta_Cases_cases___lambda__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_Meta_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_cases(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Induction(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Injection(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Cases(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Induction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Injection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1);
l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__8);
l_Lean_Meta_generalizeIndices___lambda__1___closed__1 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__1);
l_Lean_Meta_generalizeIndices___lambda__1___closed__2 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__2);
l_Lean_Meta_generalizeIndices___closed__1 = _init_l_Lean_Meta_generalizeIndices___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___closed__1);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10);
l_Lean_Meta_Cases_cases___lambda__1___closed__1 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__1);
l_Lean_Meta_Cases_cases___lambda__1___closed__2 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__2);
l_Lean_Meta_Cases_cases___lambda__1___closed__3 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__3);
l_Lean_Meta_Cases_cases___lambda__1___closed__4 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__4);
l_Lean_Meta_Cases_cases___lambda__1___closed__5 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__5);
l_Lean_Meta_Cases_cases___lambda__1___closed__6 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__6);
l_Lean_Meta_Cases_cases___lambda__1___closed__7 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__7);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

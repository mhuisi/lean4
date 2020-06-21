// Lean compiler output
// Module: Lean.Compiler.IR.ElimDeadBranches
// Imports: Init.Control.Reader Init.Data.Option Init.Data.Nat Lean.Compiler.IR.Format Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM
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
lean_object* l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__6___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3;
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_findArgValue(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(lean_object*, uint8_t, lean_object*);
lean_object* l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5;
lean_object* l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__4;
lean_object* l_Array_getD___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_UnreachableBranches_Value_beq___main(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8;
lean_object* l_Lean_IR_UnreachableBranches_Value_merge(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__1;
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_fmt___at_Lean_IR_UnreachableBranches_Value_format___main___spec__1(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___rarg(lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2___boxed(lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__4;
lean_object* l_Lean_IR_UnreachableBranches_inferMain___boxed(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_containsCtor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6;
lean_object* l_PersistentHashMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Inhabited;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_HasBeq;
lean_object* l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__19(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2;
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
uint8_t l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_projValue(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main(lean_object*);
extern lean_object* l___private_Lean_Environment_8__persistentEnvExtensionsRef;
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_interpExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4(lean_object*, size_t, size_t);
extern lean_object* l_Lean_IR_Arg_Inhabited;
lean_object* l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2(lean_object*);
extern lean_object* l_PersistentArray_getAux___main___rarg___closed__1;
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__20(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_containsCtor___main___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14;
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_Monad;
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__1;
lean_object* l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_IR_UnreachableBranches_Value_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2___boxed(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_findVarValue___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__6(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_addFunctionSummary(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(lean_object*, uint8_t, lean_object*);
extern lean_object* l_PersistentArrayNode_Inhabited___closed__1;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_beq___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_widening(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_updateCurrFnSummary(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_findVarValue(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_Inhabited;
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_projValue___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_paramInh;
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1___boxed(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_findArgValue___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_Lean_IR_UnreachableBranches_elimDead___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_interpFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__7;
extern lean_object* l_IO_Error_Inhabited___closed__1;
size_t lean_usize_modn(size_t, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__1(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__3;
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2(lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2___closed__1;
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_merge___main(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7;
lean_object* l_Lean_IR_UnreachableBranches_Value_HasToString;
lean_object* l_Lean_IR_UnreachableBranches_projValue___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_IR_UnreachableBranches_containsCtor(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Decl_Inhabited;
extern lean_object* l___private_Lean_Environment_5__envExtensionsRef;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_List_format___at_Lean_IR_UnreachableBranches_Value_format___main___spec__4(lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1;
extern lean_object* l_Lean_Format_paren___closed__1;
lean_object* l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1;
lean_object* l_mkHashMap___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__13(lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_elimDeadBranches(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2___boxed(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2(lean_object*);
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_projValue___main(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_IR_UnreachableBranches_containsCtor___main(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3;
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2(lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferStep(lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__10(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_truncate(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
uint8_t l_Lean_IR_CtorInfo_beq(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferMain___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_elimDeadBranches___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12;
lean_object* l_Lean_IR_UnreachableBranches_elimDead(lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_SMap_switch___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__18(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_inferMain(lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_interpFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2;
lean_object* l_Lean_SMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1(lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main___closed__5;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4;
lean_object* l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat;
lean_object* l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_regNamespacesExtension___closed__4;
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4;
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_IR_UnreachableBranches_Value_truncate___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2;
lean_object* l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2;
lean_object* l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1;
lean_object* l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_findVarValue___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2;
lean_object* l_mkPersistentArray___rarg(lean_object*, lean_object*);
lean_object* l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4;
lean_object* l_Array_isEqvAux___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9;
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__5(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22(lean_object*, lean_object*);
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(x_1, x_2, x_5);
x_7 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_1, x_4);
if (x_7 == 0)
{
return x_6;
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
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(x_1, x_2, x_5);
x_7 = 0;
x_8 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(x_4, x_7, x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
return x_6;
}
}
}
}
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(x_1, x_2, x_5);
x_7 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_4, x_1);
if (x_7 == 0)
{
return x_6;
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
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(x_1, x_2, x_5);
x_7 = 0;
x_8 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(x_4, x_7, x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
return x_6;
}
}
}
}
uint8_t l_Lean_IR_UnreachableBranches_Value_beq___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = l_Lean_IR_CtorInfo_beq(x_7, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_8);
x_14 = lean_array_get_size(x_10);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_isEqvAux___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1(x_8, x_10, lean_box(0), x_8, x_10, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_2, 0);
x_22 = 1;
x_23 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(x_21, x_22, x_20);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(x_20, x_22, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__4(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_Value_beq___main___spec__5(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_beq___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_UnreachableBranches_Value_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_Value_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Monad;
x_2 = l_Lean_IR_UnreachableBranches_Value_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Compiler.IR.ElimDeadBranches");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid addChoice");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2;
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(10u);
x_4 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = l_Lean_IR_CtorInfo_beq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_1, x_7, x_3);
lean_ctor_set(x_2, 1, x_12);
return x_2;
}
else
{
lean_object* x_13; 
x_13 = lean_apply_2(x_1, x_5, x_3);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = l_Lean_IR_CtorInfo_beq(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_1, x_14, x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_apply_2(x_1, x_5, x_3);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1;
x_23 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4;
x_24 = lean_panic_fn(x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1;
x_26 = l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4;
x_27 = lean_panic_fn(x_25, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_addChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = l_Lean_IR_UnreachableBranches_Value_Inhabited;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = lean_array_get(x_11, x_2, x_10);
lean_dec(x_10);
x_14 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_12, x_13);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
lean_object* _init_l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_merge___main), 2, 0);
return x_1;
}
}
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_6 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_5, x_1, x_3);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_merge___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
return x_2;
}
else
{
lean_dec(x_2);
return x_1;
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_IR_CtorInfo_beq(x_3, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_array_get_size(x_4);
x_16 = l_Array_empty___closed__1;
lean_inc(x_15);
x_17 = l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(x_4, x_6, x_15, x_15, x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_18 = lean_array_get_size(x_4);
x_19 = l_Array_empty___closed__1;
lean_inc(x_18);
x_20 = l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(x_4, x_6, x_18, x_18, x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
default: 
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_25 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_24, x_23, x_1);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_28 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_27, x_26, x_1);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_dec(x_1);
return x_2;
}
case 2:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_33 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_32, x_31, x_2);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1;
x_36 = l_Lean_IR_UnreachableBranches_Value_addChoice___main(x_35, x_34, x_2);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
default: 
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2(x_40, x_38);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2(x_42, x_38);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_fmt___at_Lean_IR_UnreachableBranches_Value_format___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = 0;
x_9 = l_Lean_Format_flatten___main___closed__1;
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = l_Lean_IR_UnreachableBranches_Value_format___main(x_7);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
lean_object* l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_IR_UnreachableBranches_Value_format___main(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_IR_UnreachableBranches_Value_format___main(x_7);
x_9 = 0;
lean_inc(x_2);
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = l_Lean_Format_joinSep___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__5(x_4, x_2);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_9);
return x_12;
}
}
}
}
lean_object* l_Lean_List_format___at_Lean_IR_UnreachableBranches_Value_format___main___spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_List_format___rarg___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lean_List_format___rarg___closed__4;
x_4 = l_Lean_Format_joinSep___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__5(x_1, x_3);
x_5 = 0;
x_6 = l_Lean_Format_sbracket___closed__2;
x_7 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
x_8 = l_Lean_Format_sbracket___closed__3;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_5);
x_10 = l_Lean_Format_sbracket___closed__1;
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_format_group(x_11);
return x_12;
}
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bot");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("top");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_HasRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_format___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__4;
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Array_isEmpty___rarg(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_box(0);
x_11 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(x_5, x_5, x_9, x_10);
lean_dec(x_5);
x_12 = 0;
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
x_14 = l_Lean_Format_paren___closed__2;
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
x_16 = l_Lean_Format_paren___closed__3;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_12);
x_18 = l_Lean_Format_paren___closed__1;
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_format_group(x_19);
x_21 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__5;
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_23);
x_25 = 0;
x_26 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__5;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_25);
return x_27;
}
}
default: 
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_List_format___at_Lean_IR_UnreachableBranches_Value_format___main___spec__4(x_28);
x_30 = 0;
x_31 = l_Lean_IR_UnreachableBranches_Value_format___main___closed__7;
x_32 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_30);
return x_32;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_Value_format___main___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at_Lean_IR_UnreachableBranches_Value_format___main___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_format(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_Value_format___main(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_Value_format), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_Value_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1;
return x_1;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_11, x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_10, x_3, x_15);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_16;
goto _start;
}
}
}
lean_object* l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_6, x_2);
x_9 = l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_10, x_2);
x_13 = l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
uint8_t l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_1, x_4);
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
lean_object* l_Lean_IR_UnreachableBranches_Value_truncate___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_Lean_Name_getPrefix(x_7);
lean_dec(x_7);
x_9 = l_Lean_NameSet_contains(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_17; 
lean_inc(x_8);
lean_inc(x_1);
x_17 = lean_environment_find(x_1, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_8);
x_10 = x_3;
goto block_16;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 5)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*5);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_8);
x_10 = x_3;
goto block_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_8, x_21);
x_10 = x_22;
goto block_16;
}
}
else
{
lean_dec(x_18);
lean_dec(x_8);
x_10 = x_3;
goto block_16;
}
}
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = x_5;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__1(x_1, x_10, x_12, x_11);
x_14 = x_13;
if (lean_is_scalar(x_6)) {
 x_15 = lean_alloc_ctor(2, 2, 0);
} else {
 x_15 = x_6;
}
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(1);
return x_23;
}
}
case 3:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(x_1, x_3, x_25);
x_27 = lean_box(1);
x_28 = l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(x_27, x_26);
if (x_28 == 0)
{
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_29; 
lean_dec(x_26);
lean_free_object(x_2);
x_29 = lean_box(1);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_List_map___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__2(x_1, x_3, x_30);
x_32 = lean_box(1);
x_33 = l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_31);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_31);
x_35 = lean_box(1);
return x_35;
}
}
}
default: 
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_IR_UnreachableBranches_Value_truncate___main___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_truncate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_Value_widening(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_3);
x_5 = l_Lean_NameSet_empty;
x_6 = l_Lean_IR_UnreachableBranches_Value_truncate___main(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = lean_name_eq(x_3, x_17);
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
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_21 = lean_name_eq(x_4, x_19);
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
x_28 = lean_name_eq(x_4, x_26);
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
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_40, x_41, x_42, x_4, x_5);
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
x_63 = lean_name_eq(x_4, x_60);
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
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_71, x_73, x_74, x_4, x_5);
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
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__4(x_1, x_82, x_4, x_5);
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
x_92 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5(x_3, x_89, x_90, x_89, x_82, x_91);
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
lean_object* l_PersistentHashMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_5, x_7, x_8, x_2, x_3);
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
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_12, x_14, x_15, x_2, x_3);
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
uint8_t l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__10(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__9(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__8(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(x_2, x_3, x_10);
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
x_26 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__8(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__11(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_PersistentHashMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__2(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_PersistentHashMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__2(x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__6(x_13, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__6(x_15, x_2, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
lean_object* l_mkHashMap___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_SMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__1(x_4, x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16(x_7, x_7, x_8, x_4);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_SMap_switch___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__18(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
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
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_get(x_13, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_19);
x_23 = x_19;
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_io_ref_reset(x_13, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_io_ref_set(x_13, x_24, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_19);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_19);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_19);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
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
}
else
{
uint8_t x_48; 
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
return x_3;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22(x_18, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set(x_22, 5, x_16);
x_23 = lean_io_ref_get(x_3, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_22);
x_26 = x_22;
x_27 = lean_array_push(x_24, x_26);
x_28 = lean_io_ref_reset(x_3, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_io_ref_set(x_3, x_27, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_22);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_27);
lean_dec(x_22);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_22);
x_43 = !lean_is_exclusive(x_23);
if (x_43 == 0)
{
return x_23;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_23, 0);
x_45 = lean_ctor_get(x_23, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_23);
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_51);
x_54 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_58);
return x_4;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_array_get_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(x_1, x_59, x_59, x_61, x_62);
lean_dec(x_61);
lean_dec(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 5);
lean_inc(x_69);
lean_dec(x_1);
x_70 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_71 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_71, 0, x_65);
lean_closure_set(x_71, 1, x_70);
x_72 = l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22(x_71, x_60);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_68);
lean_ctor_set(x_75, 5, x_69);
x_76 = lean_io_ref_get(x_3, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_75);
x_79 = x_75;
x_80 = lean_array_push(x_77, x_79);
x_81 = lean_io_ref_reset(x_3, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_io_ref_set(x_3, x_80, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_75);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_89 = x_83;
} else {
 lean_dec_ref(x_83);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_80);
lean_dec(x_75);
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_75);
x_95 = lean_ctor_get(x_76, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_76, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_97 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
x_99 = lean_ctor_get(x_72, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_72, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_101 = x_72;
} else {
 lean_dec_ref(x_72);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
lean_dec(x_1);
x_104 = l_Lean_Name_toString___closed__1;
x_105 = l_Lean_Name_toStringWithSep___main(x_104, x_103);
x_106 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_107 = lean_string_append(x_106, x_105);
lean_dec(x_105);
x_108 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_109 = lean_string_append(x_107, x_108);
x_110 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_60);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_4);
if (x_112 == 0)
{
return x_4;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_4);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__19(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
lean_inc(x_4);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__20(x_14, x_2);
return x_15;
}
}
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_SMap_insert___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__1(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12;
x_4 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(x_1, x_1, x_2, x_3);
x_5 = l_Lean_SMap_switch___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__18(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachBranchesFunSummary");
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2;
x_2 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3;
x_3 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4;
x_4 = l_Lean_regNamespacesExtension___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__19(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__5(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__16(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__17(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__15(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__21(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_HashMap_Inhabited___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4;
x_2 = lean_box(0);
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5;
x_4 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6;
x_5 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7;
x_6 = l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8;
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
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_addFunctionSummary(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_IR_UnreachableBranches_functionSummariesExt;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_PersistentHashMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__5(x_4, x_2);
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
x_9 = l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_IR_UnreachableBranches_functionSummariesExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
x_5 = l_Lean_SMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__1(x_4, x_2);
return x_5;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_nat_dec_eq(x_4, x_1);
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
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_IR_UnreachableBranches_findVarValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_HashMap_Inhabited___closed__1;
x_7 = lean_array_get(x_6, x_4, x_5);
lean_dec(x_4);
x_8 = l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(x_7, x_1);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find_x3f___main___at_Lean_IR_UnreachableBranches_findVarValue___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_findVarValue___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_findVarValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_findVarValue(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_findArgValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_UnreachableBranches_findVarValue(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_findArgValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_findArgValue(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_mkHashMap___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
uint8_t l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_nat_dec_eq(x_4, x_1);
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
lean_object* l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_usize_of_nat(x_4);
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
x_16 = lean_usize_of_nat(x_12);
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__6(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(x_1, x_2, x_7);
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
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_usize_of_nat(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__4(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(x_2, x_3, x_10);
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
x_23 = lean_usize_of_nat(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__4(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* _init_l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_UnreachableBranches_findVarValue(x_1, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_array_fget(x_10, x_11);
x_16 = l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1;
x_17 = lean_array_fset(x_10, x_11, x_16);
x_18 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_9);
x_19 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_15, x_1, x_18);
x_20 = lean_array_fset(x_17, x_11, x_19);
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_box(0);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_array_get_size(x_23);
x_27 = lean_nat_dec_lt(x_25, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_box(0);
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_29);
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_array_fget(x_23, x_25);
x_31 = l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1;
x_32 = lean_array_fset(x_23, x_25, x_31);
x_33 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_22);
x_34 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_30, x_1, x_33);
x_35 = lean_array_fset(x_32, x_25, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
x_37 = lean_box(0);
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_37);
return x_5;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_5, 1);
x_39 = lean_ctor_get(x_5, 0);
lean_inc(x_38);
lean_inc(x_39);
lean_dec(x_5);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_array_get_size(x_40);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_array_fget(x_40, x_43);
x_50 = l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1;
x_51 = lean_array_fset(x_40, x_43, x_50);
x_52 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_39);
x_53 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_49, x_1, x_52);
x_54 = lean_array_fset(x_51, x_43, x_53);
if (lean_is_scalar(x_42)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_42;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_41);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateVarAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_IR_UnreachableBranches_projValue___main(x_4, x_1);
x_7 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_2, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_projValue___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_box(0);
x_5 = l_Array_getD___rarg(x_3, x_2, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_box(0);
x_8 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1(x_2, x_7, x_6);
return x_8;
}
default: 
{
lean_inc(x_1);
return x_1;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___main___at_Lean_IR_UnreachableBranches_projValue___main___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_UnreachableBranches_projValue___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_projValue___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_projValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_projValue___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_projValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_projValue(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
x_13 = l_Lean_IR_UnreachableBranches_findArgValue(x_12, x_3, x_4);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = x_14;
x_19 = lean_array_fset(x_11, x_1, x_18);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_19;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_IR_Decl_name(x_7);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = x_2 >> x_3;
x_6 = lean_usize_to_nat(x_5);
x_7 = l_PersistentArray_getAux___main___rarg___closed__1;
x_8 = lean_array_get(x_7, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_9 = 1;
x_10 = x_9 << x_3;
x_11 = x_10 - x_9;
x_12 = x_2 & x_11;
x_13 = 5;
x_14 = x_3 - x_13;
x_1 = x_8;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_usize_to_nat(x_2);
x_18 = l_Lean_IR_UnreachableBranches_Value_Inhabited;
x_19 = lean_array_get(x_18, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_usize_of_nat(x_2);
x_7 = lean_ctor_get_usize(x_1, 4);
lean_dec(x_1);
x_8 = l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4(x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
x_11 = l_Lean_IR_UnreachableBranches_Value_Inhabited;
x_12 = lean_array_get(x_11, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_interpExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = x_5;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1___boxed), 4, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = x_8;
x_10 = lean_apply_2(x_9, x_2, x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Lean_IR_UnreachableBranches_findVarValue(x_19, x_2, x_3);
lean_dec(x_2);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_IR_UnreachableBranches_projValue___main(x_22, x_18);
lean_dec(x_18);
lean_dec(x_22);
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
x_26 = l_Lean_IR_UnreachableBranches_projValue___main(x_24, x_18);
lean_dec(x_18);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = l_Lean_IR_UnreachableBranches_getFunctionSummary_x3f(x_29, x_28);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2(x_28, x_31, x_32);
lean_dec(x_31);
lean_dec(x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
x_38 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_37, x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
lean_dec(x_2);
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
default: 
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentArray_getAux___main___at_Lean_IR_UnreachableBranches_interpExpr___spec__4(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(x_1, x_2, x_5);
x_7 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_4, x_1);
if (x_7 == 0)
{
return x_6;
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
uint8_t l_Lean_IR_UnreachableBranches_containsCtor___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
case 2:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_IR_CtorInfo_beq(x_5, x_2);
return x_6;
}
default: 
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 0;
x_9 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(x_2, x_8, x_7);
return x_9;
}
}
}
}
lean_object* l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_IR_UnreachableBranches_containsCtor___main___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_IR_UnreachableBranches_containsCtor___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_UnreachableBranches_containsCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_containsCtor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnreachableBranches_containsCtor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = x_4 >> x_5;
x_9 = 1;
x_10 = x_9 << x_5;
x_11 = x_10 - x_9;
x_12 = x_4 & x_11;
x_13 = 5;
x_14 = x_5 - x_13;
x_15 = lean_usize_to_nat(x_8);
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_7, x_15);
x_19 = l_PersistentArrayNode_Inhabited___closed__1;
x_20 = lean_array_fset(x_7, x_15, x_19);
x_21 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_18, x_12, x_14);
x_22 = lean_array_fset(x_20, x_15, x_21);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = x_4 >> x_5;
x_25 = 1;
x_26 = x_25 << x_5;
x_27 = x_26 - x_25;
x_28 = x_4 & x_27;
x_29 = 5;
x_30 = x_5 - x_29;
x_31 = lean_usize_to_nat(x_24);
x_32 = lean_array_get_size(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_array_fget(x_23, x_31);
x_36 = l_PersistentArrayNode_Inhabited___closed__1;
x_37 = lean_array_fset(x_23, x_31, x_36);
x_38 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_35, x_28, x_30);
x_39 = lean_array_fset(x_37, x_31, x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_usize_to_nat(x_4);
x_44 = lean_array_get_size(x_42);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_array_fget(x_42, x_43);
x_47 = lean_box(1);
x_48 = lean_array_fset(x_42, x_43, x_47);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_IR_UnreachableBranches_Value_widening(x_49, x_1, x_46);
x_51 = lean_array_fset(x_48, x_43, x_50);
lean_dec(x_43);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
lean_dec(x_3);
x_53 = lean_usize_to_nat(x_4);
x_54 = lean_array_get_size(x_52);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_array_fget(x_52, x_53);
x_58 = lean_box(1);
x_59 = lean_array_fset(x_52, x_53, x_58);
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_dec(x_2);
x_61 = l_Lean_IR_UnreachableBranches_Value_widening(x_60, x_1, x_57);
x_62 = lean_array_fset(x_59, x_53, x_61);
lean_dec(x_53);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
}
lean_object* l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_usize(x_3, 4);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_nat_dec_le(x_9, x_4);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; 
x_11 = lean_usize_of_nat(x_4);
x_12 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_6, x_11, x_8);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_4, x_9);
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_box(1);
x_18 = lean_array_fset(x_7, x_13, x_17);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_IR_UnreachableBranches_Value_widening(x_19, x_1, x_16);
x_21 = lean_array_fset(x_18, x_13, x_20);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_21);
return x_3;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get_usize(x_3, 4);
x_26 = lean_ctor_get(x_3, 3);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_27 = lean_nat_dec_le(x_26, x_4);
if (x_27 == 0)
{
size_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_4);
x_29 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_22, x_28, x_25);
x_30 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set_usize(x_30, 4, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_nat_sub(x_4, x_26);
x_32 = lean_array_get_size(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set_usize(x_34, 4, x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_array_fget(x_23, x_31);
x_36 = lean_box(1);
x_37 = lean_array_fset(x_23, x_31, x_36);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Lean_IR_UnreachableBranches_Value_widening(x_38, x_1, x_35);
x_40 = lean_array_fset(x_37, x_31, x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_24);
lean_ctor_set(x_41, 3, x_26);
lean_ctor_set_usize(x_41, 4, x_25);
return x_41;
}
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateCurrFnSummary(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(x_1, x_2, x_6, x_4);
lean_dec(x_4);
lean_ctor_set(x_3, 1, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(x_1, x_2, x_11, x_4);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_PersistentArray_modifyAux___main___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__2(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
lean_object* l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_modify___at_Lean_IR_UnreachableBranches_updateCurrFnSummary___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = lean_nat_sub(x_4, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = l_Lean_IR_paramInh;
x_16 = lean_array_get(x_15, x_1, x_14);
x_17 = l_Lean_IR_Arg_Inhabited;
x_18 = lean_array_get(x_17, x_2, x_14);
lean_dec(x_14);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_IR_UnreachableBranches_findVarValue(x_19, x_7, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_IR_UnreachableBranches_findArgValue(x_18, x_7, x_22);
lean_dec(x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_21);
x_26 = l_Lean_IR_UnreachableBranches_Value_merge___main(x_21, x_24);
x_27 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_26, x_21);
lean_dec(x_21);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_3, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_26);
lean_dec(x_19);
x_32 = 1;
x_5 = x_12;
x_6 = x_32;
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_array_fget(x_29, x_3);
x_35 = l_HashMap_Inhabited___closed__1;
x_36 = lean_array_fset(x_29, x_3, x_35);
x_37 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_34, x_19, x_26);
x_38 = lean_array_fset(x_36, x_3, x_37);
lean_ctor_set(x_25, 0, x_38);
x_39 = 1;
x_5 = x_12;
x_6 = x_39;
x_8 = x_25;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_array_get_size(x_41);
x_44 = lean_nat_dec_lt(x_3, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_26);
lean_dec(x_19);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
x_46 = 1;
x_5 = x_12;
x_6 = x_46;
x_8 = x_45;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_array_fget(x_41, x_3);
x_49 = l_HashMap_Inhabited___closed__1;
x_50 = lean_array_fset(x_41, x_3, x_49);
x_51 = l_HashMapImp_insert___at_Lean_IR_UnreachableBranches_updateVarAssignment___spec__2(x_48, x_19, x_26);
x_52 = lean_array_fset(x_50, x_3, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
x_54 = 1;
x_5 = x_12;
x_6 = x_54;
x_8 = x_53;
goto _start;
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_19);
x_5 = x_12;
x_8 = x_25;
goto _start;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_5);
x_57 = lean_box(x_6);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_8);
return x_58;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_array_get_size(x_1);
x_7 = 0;
lean_inc(x_6);
x_8 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1(x_1, x_2, x_5, x_6, x_6, x_7, x_3, x_4);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_updateJPParamsAssignment___spec__1(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_IR_UnreachableBranches_updateJPParamsAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_1, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_dec(x_14);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_4);
x_17 = l_Lean_IR_UnreachableBranches_interpFnBody___main(x_14, x_4, x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_3 = x_12;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
lean_inc(x_4);
x_21 = l_Lean_IR_UnreachableBranches_interpFnBody___main(x_20, x_4, x_5);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_3 = x_12;
x_5 = x_22;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_interpFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_2);
x_14 = l_Lean_IR_UnreachableBranches_interpExpr(x_12, x_2, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_11, x_15, x_2, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_1 = x_13;
x_3 = x_18;
goto _start;
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_2, 3);
x_26 = l_Lean_IR_LocalContext_addJP(x_25, x_20, x_21, x_22);
lean_ctor_set(x_2, 3, x_26);
x_1 = x_23;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_32 = l_Lean_IR_LocalContext_addJP(x_31, x_20, x_21, x_22);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
x_1 = x_23;
x_2 = x_33;
goto _start;
}
}
case 10:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_IR_UnreachableBranches_findVarValue(x_35, x_2, x_3);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1(x_38, x_36, x_40, x_2, x_39);
lean_dec(x_36);
lean_dec(x_38);
return x_41;
}
case 11:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_IR_UnreachableBranches_findArgValue(x_42, x_2, x_3);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_IR_UnreachableBranches_updateCurrFnSummary(x_44, x_2, x_45);
return x_46;
}
case 12:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_ctor_get(x_2, 3);
lean_inc(x_49);
x_50 = l_Lean_IR_LocalContext_getJPParams(x_49, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = l_Array_empty___closed__1;
x_52 = l_Option_get_x21___rarg___closed__3;
x_53 = lean_panic_fn(x_51, x_52);
x_54 = l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(x_53, x_48, x_2, x_3);
lean_dec(x_48);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_54, 0, x_59);
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_dec(x_54);
x_64 = l_Lean_IR_LocalContext_getJPBody(x_49, x_47);
lean_dec(x_47);
lean_dec(x_49);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lean_IR_Inhabited;
x_66 = lean_panic_fn(x_65, x_52);
x_1 = x_66;
x_3 = x_63;
goto _start;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_1 = x_68;
x_3 = x_63;
goto _start;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_50, 0);
lean_inc(x_70);
lean_dec(x_50);
x_71 = l_Lean_IR_UnreachableBranches_updateJPParamsAssignment(x_70, x_48, x_2, x_3);
lean_dec(x_48);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_71, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_71, 0, x_76);
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_dec(x_71);
x_81 = l_Lean_IR_LocalContext_getJPBody(x_49, x_47);
lean_dec(x_47);
lean_dec(x_49);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = l_Lean_IR_Inhabited;
x_83 = l_Option_get_x21___rarg___closed__3;
x_84 = lean_panic_fn(x_82, x_83);
x_1 = x_84;
x_3 = x_80;
goto _start;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
lean_dec(x_81);
x_1 = x_86;
x_3 = x_80;
goto _start;
}
}
}
}
default: 
{
lean_object* x_88; 
x_88 = lean_box(0);
x_4 = x_88;
goto block_10;
}
}
block_10:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_interpFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_UnreachableBranches_interpFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UnreachableBranches_interpFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(1);
x_14 = l_Lean_IR_UnreachableBranches_updateVarAssignment(x_12, x_13, x_3, x_4);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_2 = x_11;
x_4 = x_15;
goto _start;
}
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HashMap_Inhabited___closed__1;
x_2 = x_1;
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
x_10 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2___closed__1;
x_11 = lean_array_fset(x_7, x_1, x_10);
lean_dec(x_1);
x_1 = x_9;
x_2 = x_11;
goto _start;
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_Lean_IR_Decl_Inhabited;
x_15 = lean_array_get(x_14, x_13, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
x_19 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_18, x_12);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_12);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(x_16, x_7, x_23, x_6);
lean_dec(x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_IR_UnreachableBranches_interpFnBody___main(x_17, x_23, x_25);
if (x_4 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_28, x_12);
lean_dec(x_12);
x_30 = l_Lean_IR_UnreachableBranches_Value_beq___main(x_19, x_29);
lean_dec(x_29);
lean_dec(x_19);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 1;
x_3 = x_10;
x_4 = x_31;
x_6 = x_27;
goto _start;
}
else
{
uint8_t x_33; 
x_33 = 0;
x_3 = x_10;
x_4 = x_33;
x_6 = x_27;
goto _start;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_12);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = 1;
x_3 = x_10;
x_4 = x_36;
x_6 = x_35;
goto _start;
}
}
else
{
lean_dec(x_15);
lean_dec(x_12);
x_3 = x_10;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_39 = lean_box(x_4);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferStep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
x_5 = x_3;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(x_6, x_5);
x_8 = x_7;
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_8);
x_11 = 0;
lean_inc(x_4);
x_12 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(x_1, x_4, x_4, x_11, x_1, x_2);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = 0;
lean_inc(x_4);
x_16 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(x_1, x_4, x_4, x_15, x_1, x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Nat_foldMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__3(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = l_Lean_IR_UnreachableBranches_inferStep(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_2 = x_12;
goto _start;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_inferMain___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_inferMain___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_inferMain___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_UnreachableBranches_inferMain___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_IR_UnreachableBranches_inferMain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_UnreachableBranches_inferMain(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_box(0);
x_17 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_16, x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_18 = lean_box(13);
lean_ctor_set(x_10, 1, x_18);
x_19 = x_10;
x_20 = lean_array_fset(x_9, x_2, x_19);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_15);
lean_ctor_set(x_10, 1, x_22);
x_23 = x_10;
x_24 = lean_array_fset(x_9, x_2, x_23);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_box(0);
x_29 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_28, x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
x_30 = lean_box(13);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = x_31;
x_33 = lean_array_fset(x_9, x_2, x_32);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_37 = x_36;
x_38 = lean_array_fset(x_9, x_2, x_37);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_38;
goto _start;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_41);
lean_ctor_set(x_10, 0, x_42);
x_43 = x_10;
x_44 = lean_array_fset(x_9, x_2, x_43);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_44;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_10, 0);
lean_inc(x_46);
lean_dec(x_10);
x_47 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = x_48;
x_50 = lean_array_fset(x_9, x_2, x_49);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_50;
goto _start;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
x_17 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_2, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_18 = lean_box(13);
lean_ctor_set(x_11, 1, x_18);
x_19 = x_11;
x_20 = lean_array_fset(x_10, x_3, x_19);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_16);
lean_ctor_set(x_11, 1, x_22);
x_23 = x_11;
x_24 = lean_array_fset(x_10, x_3, x_23);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = l_Lean_IR_UnreachableBranches_containsCtor___main(x_2, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
x_29 = lean_box(13);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = x_30;
x_32 = lean_array_fset(x_10, x_3, x_31);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
x_36 = x_35;
x_37 = lean_array_fset(x_10, x_3, x_36);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_37;
goto _start;
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_40);
lean_ctor_set(x_11, 0, x_41);
x_42 = x_11;
x_43 = lean_array_fset(x_10, x_3, x_42);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
lean_dec(x_11);
x_46 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = x_47;
x_49 = lean_array_fset(x_10, x_3, x_48);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_49;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 3);
x_13 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_12);
lean_ctor_set(x_2, 3, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_18 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
return x_19;
}
}
case 1:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_21);
x_24 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_22);
lean_ctor_set(x_2, 3, x_24);
lean_ctor_set(x_2, 2, x_23);
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_29 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_27);
x_30 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_28);
x_31 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
return x_31;
}
}
case 10:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 3);
x_35 = x_34;
x_36 = l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(x_1, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(x_1, x_37, x_35);
x_39 = x_38;
lean_ctor_set(x_2, 3, x_39);
return x_2;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(x_1, x_40, x_41, x_35);
lean_dec(x_40);
x_43 = x_42;
lean_ctor_set(x_2, 3, x_43);
return x_2;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_2, 2);
x_47 = lean_ctor_get(x_2, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_2);
x_48 = x_47;
x_49 = l_HashMapImp_find_x3f___at_Lean_IR_UnreachableBranches_findVarValue___spec__1(x_1, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(x_1, x_50, x_48);
x_52 = x_51;
x_53 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(x_1, x_54, x_55, x_48);
lean_dec(x_54);
x_57 = x_56;
x_58 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_45);
lean_ctor_set(x_58, 2, x_46);
lean_ctor_set(x_58, 3, x_57);
return x_58;
}
}
}
default: 
{
lean_object* x_59; 
x_59 = lean_box(0);
x_3 = x_59;
goto block_10;
}
}
block_10:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_IR_FnBody_body(x_2);
x_6 = lean_box(13);
x_7 = l_Lean_IR_FnBody_setBody(x_2, x_6);
x_8 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_5);
x_9 = l_Lean_IR_FnBody_setBody(x_7, x_8);
return x_9;
}
else
{
return x_2;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_elimDeadAux___main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDeadAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDeadAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDead(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_4);
lean_ctor_set(x_2, 3, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_10 = l_Lean_IR_UnreachableBranches_elimDeadAux___main(x_1, x_9);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_IR_UnreachableBranches_elimDead___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UnreachableBranches_elimDead(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_HashMap_Inhabited___closed__1;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = l_Lean_IR_UnreachableBranches_elimDead(x_12, x_10);
lean_dec(x_12);
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
lean_object* l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = l_Lean_IR_Decl_Inhabited;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = l_Lean_IR_Decl_name(x_12);
lean_dec(x_12);
lean_inc(x_2);
x_14 = l_PersistentArray_get_x21___at_Lean_IR_UnreachableBranches_interpExpr___spec__3(x_2, x_10);
lean_dec(x_10);
x_15 = l_Lean_IR_UnreachableBranches_addFunctionSummary(x_5, x_13, x_14);
x_4 = x_9;
x_5 = x_15;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
}
lean_object* l_Lean_IR_elimDeadBranches(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_1);
x_6 = x_1;
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_8 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(x_7, x_6);
x_9 = x_8;
x_10 = lean_array_get_size(x_1);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = l_mkPersistentArray___rarg(x_10, x_11);
x_13 = lean_box(0);
lean_inc(x_5);
lean_inc(x_1);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_12);
x_16 = l_Lean_IR_UnreachableBranches_inferMain___main___rarg(x_14, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__1(x_19, x_7, x_6);
lean_dec(x_19);
x_21 = x_20;
lean_inc(x_10);
x_22 = l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__2(x_1, x_18, x_10, x_10, x_5);
lean_dec(x_10);
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
lean_inc(x_1);
x_26 = x_1;
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
x_28 = l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2(x_27, x_26);
x_29 = x_28;
x_30 = lean_array_get_size(x_1);
x_31 = lean_box(0);
lean_inc(x_30);
x_32 = l_mkPersistentArray___rarg(x_30, x_31);
x_33 = lean_box(0);
lean_inc(x_24);
lean_inc(x_1);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_1);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
x_36 = l_Lean_IR_UnreachableBranches_inferMain___main___rarg(x_34, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__1(x_39, x_27, x_26);
lean_dec(x_39);
x_41 = x_40;
lean_inc(x_30);
x_42 = l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__2(x_1, x_38, x_30, x_30, x_24);
lean_dec(x_30);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_25);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_elimDeadBranches___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_IR_elimDeadBranches___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_elimDeadBranches___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Data_Option(lean_object*);
lean_object* initialize_Init_Data_Nat(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_IR_ElimDeadBranches(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_UnreachableBranches_Value_Inhabited = _init_l_Lean_IR_UnreachableBranches_Value_Inhabited();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_Inhabited);
l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_HasBeq___closed__1);
l_Lean_IR_UnreachableBranches_Value_HasBeq = _init_l_Lean_IR_UnreachableBranches_Value_HasBeq();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_HasBeq);
l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__1);
l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2 = _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__2);
l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3 = _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__3);
l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4 = _init_l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_addChoice___main___closed__4);
l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1 = _init_l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1();
lean_mark_persistent(l_List_foldl___main___at_Lean_IR_UnreachableBranches_Value_merge___main___spec__2___closed__1);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__1);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__2 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__2();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__2);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__3 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__3();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__3);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__4 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__4();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__4);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__5 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__5();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__5);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__6 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__6();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__6);
l_Lean_IR_UnreachableBranches_Value_format___main___closed__7 = _init_l_Lean_IR_UnreachableBranches_Value_format___main___closed__7();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_format___main___closed__7);
l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat___closed__1);
l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat = _init_l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_Lean_HasFormat);
l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1 = _init_l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_HasToString___closed__1);
l_Lean_IR_UnreachableBranches_Value_HasToString = _init_l_Lean_IR_UnreachableBranches_Value_HasToString();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_Value_HasToString);
l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14 = _init_l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__14);
l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1 = _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__1);
l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2 = _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12___closed__2);
l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12 = _init_l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__12);
l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___spec__22___closed__2);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__1);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__2);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__3);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__4);
l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5 = _init_l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension___closed__5);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__1);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__2);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__3);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__4);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__5);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__6);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__7);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__8);
l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9 = _init_l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt___closed__9);
res = l_Lean_IR_UnreachableBranches_mkFunctionSummariesExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_UnreachableBranches_functionSummariesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_UnreachableBranches_functionSummariesExt);
lean_dec_ref(res);
l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1 = _init_l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1();
lean_mark_persistent(l_Lean_IR_UnreachableBranches_updateVarAssignment___closed__1);
l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2___closed__1 = _init_l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_IR_UnreachableBranches_inferStep___spec__2___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

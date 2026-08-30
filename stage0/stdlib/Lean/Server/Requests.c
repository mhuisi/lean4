// Lean compiler output
// Module: Lean.Server.Requests
// Imports: public import Lean.Server.RequestCancellation public import Lean.Server.FileSource public import Lean.Server.FileWorker.Utils public import Std.Sync.Mutex
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
uint64_t lean_string_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_EIO_asTask___redArg(lean_object*);
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*);
static const lean_string_object l_Lean_Server_instInhabitedRequestError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Server_instInhabitedRequestError_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value;
static const lean_ctor_object l_Lean_Server_instInhabitedRequestError_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_instInhabitedRequestError_default___closed__1 = (const lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedRequestError_default = (const lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedRequestError = (const lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__1_value;
static const lean_string_object l_Lean_Server_RequestError_fileChanged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "File changed."};
static const lean_object* l_Lean_Server_RequestError_fileChanged___closed__0 = (const lean_object*)&l_Lean_Server_RequestError_fileChanged___closed__0_value;
static const lean_ctor_object l_Lean_Server_RequestError_fileChanged___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_RequestError_fileChanged___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_RequestError_fileChanged___closed__1 = (const lean_object*)&l_Lean_Server_RequestError_fileChanged___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_RequestError_fileChanged = (const lean_object*)&l_Lean_Server_RequestError_fileChanged___closed__1_value;
static const lean_string_object l_Lean_Server_RequestError_methodNotFound___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "No request handler found for '"};
static const lean_object* l_Lean_Server_RequestError_methodNotFound___closed__0 = (const lean_object*)&l_Lean_Server_RequestError_methodNotFound___closed__0_value;
static const lean_string_object l_Lean_Server_RequestError_methodNotFound___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Server_RequestError_methodNotFound___closed__1 = (const lean_object*)&l_Lean_Server_RequestError_methodNotFound___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_invalidParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_internalError(lean_object*);
static const lean_ctor_object l_Lean_Server_RequestError_requestCancelled___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_RequestError_requestCancelled___closed__0 = (const lean_object*)&l_Lean_Server_RequestError_requestCancelled___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_RequestError_requestCancelled = (const lean_object*)&l_Lean_Server_RequestError_requestCancelled___closed__0_value;
static const lean_string_object l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Outdated RPC session"};
static const lean_object* l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0 = (const lean_object*)&l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value;
static const lean_ctor_object l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_RequestError_rpcNeedsReconnect___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1 = (const lean_object*)&l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_RequestError_rpcNeedsReconnect = (const lean_object*)&l_Lean_Server_RequestError_rpcNeedsReconnect___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_parseRequestParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot parse request params: "};
static const lean_object* l_Lean_Server_parseRequestParams___redArg___closed__0 = (const lean_object*)&l_Lean_Server_parseRequestParams___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_parseRequestParams___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Server_parseRequestParams___redArg___closed__1 = (const lean_object*)&l_Lean_Server_parseRequestParams___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_instInhabitedRequestError_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object*);
static lean_once_cell_t l_Lean_Server_instInhabitedServerRequestResponse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedServerRequestResponse___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instMonadLiftIORequestM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instMonadLiftIORequestM___closed__0 = (const lean_object*)&l_Lean_Server_instMonadLiftIORequestM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instMonadLiftIORequestM = (const lean_object*)&l_Lean_Server_instMonadLiftIORequestM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0 = (const lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM = (const lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0 = (const lean_object*)&l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM = (const lean_object*)&l_Lean_Server_instMonadLiftCancellableMRequestM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Cannot parse server request response: "};
static const lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "no snapshot found at "};
static const lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0 = (const lean_object*)&l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1 = (const lean_object*)&l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1_value;
static const lean_string_object l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2 = (const lean_object*)&l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2_value;
static const lean_string_object l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3 = (const lean_object*)&l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\"id\":"};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "\"jsonrpc\":\"2.0\","};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\"result\":"};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4_value;
static const lean_string_object l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5 = (const lean_object*)&l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_requestHandlers;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__1_value;
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__2 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__3;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___redArg___closed__4 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Failed to parse original LSP response for `"};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` when chaining: "};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Failed to parse original LSP response JSON for `"};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Failed to chain LSP request handler for '"};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___closed__0 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_chainLspRequestHandler___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "': no initial handler registered"};
static const lean_object* l_Lean_Server_chainLspRequestHandler___redArg___closed__1 = (const lean_object*)&l_Lean_Server_chainLspRequestHandler___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_statefulRequestHandlers;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Got invalid state type in stateful LSP request handler for "};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__6_value),((lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__8_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__4_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__10_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__11_value),((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__5_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__12_value),((lean_object*)&l_Lean_Server_instMonadLiftEIOExceptionRequestM___closed__0_value)} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods();
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "Failed to convert response of previous request handler when chaining stateful LSP request handlers"};
static const lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1;
static const lean_string_object l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "Failed to parse response of previous request handler when chaining stateful LSP request handlers"};
static const lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Failed to chain stateful LSP request handler for '"};
static const lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0 = (const lean_object*)&l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_handleLspRequest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "request '"};
static const lean_object* l_Lean_Server_handleLspRequest___closed__0 = (const lean_object*)&l_Lean_Server_handleLspRequest___closed__0_value;
static const lean_string_object l_Lean_Server_handleLspRequest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "' routed through watchdog but unknown in worker; are both using the same plugins\?"};
static const lean_object* l_Lean_Server_handleLspRequest___closed__1 = (const lean_object*)&l_Lean_Server_handleLspRequest___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object* v_method_14_){
_start:
{
uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_15_ = 2;
v___x_16_ = ((lean_object*)(l_Lean_Server_RequestError_methodNotFound___closed__0));
v___x_17_ = lean_string_append(v___x_16_, v_method_14_);
v___x_18_ = ((lean_object*)(l_Lean_Server_RequestError_methodNotFound___closed__1));
v___x_19_ = lean_string_append(v___x_17_, v___x_18_);
v___x_20_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*1, v___x_15_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object* v_method_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Server_RequestError_methodNotFound(v_method_21_);
lean_dec_ref(v_method_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_invalidParams(lean_object* v_message_23_){
_start:
{
uint8_t v___x_24_; lean_object* v___x_25_; 
v___x_24_ = 3;
v___x_25_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_25_, 0, v_message_23_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*1, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_internalError(lean_object* v_message_26_){
_start:
{
uint8_t v___x_27_; lean_object* v___x_28_; 
v___x_27_ = 4;
v___x_28_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_28_, 0, v_message_26_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*1, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException(lean_object* v_e_38_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = l_Lean_Exception_toMessageData(v_e_38_);
v___x_41_ = l_Lean_MessageData_toString(v___x_40_);
v___x_42_ = l_Lean_Server_RequestError_internalError(v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofException___boxed(lean_object* v_e_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Server_RequestError_ofException(v_e_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_ofIoError(lean_object* v_e_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_io_error_to_string(v_e_47_);
v___x_49_ = l_Lean_Server_RequestError_internalError(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object* v_id_50_, lean_object* v_e_51_){
_start:
{
uint8_t v_code_52_; lean_object* v_message_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_code_52_ = lean_ctor_get_uint8(v_e_51_, sizeof(void*)*1);
v_message_53_ = lean_ctor_get(v_e_51_, 0);
v___x_54_ = lean_box(0);
lean_inc_ref(v_message_53_);
v___x_55_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_55_, 0, v_id_50_);
lean_ctor_set(v___x_55_, 1, v_message_53_);
lean_ctor_set(v___x_55_, 2, v___x_54_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*3, v_code_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object* v_id_56_, lean_object* v_e_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Server_RequestError_toLspResponseError(v_id_56_, v_e_57_);
lean_dec_ref(v_e_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___redArg(lean_object* v_inst_61_, lean_object* v_params_62_){
_start:
{
lean_object* v___x_63_; 
lean_inc(v_params_62_);
v___x_63_ = lean_apply_1(v_inst_61_, v_params_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_79_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_79_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_79_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_79_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_68_ = 3;
v___x_69_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__0));
v___x_70_ = l_Lean_Json_compress(v_params_62_);
v___x_71_ = lean_string_append(v___x_69_, v___x_70_);
lean_dec_ref(v___x_70_);
v___x_72_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_73_ = lean_string_append(v___x_71_, v___x_72_);
v___x_74_ = lean_string_append(v___x_73_, v_a_64_);
lean_dec(v_a_64_);
v___x_75_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_68_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_75_);
v___x_77_ = v___x_66_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
lean_dec(v_params_62_);
v_a_80_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_63_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_63_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object* v_paramType_88_, lean_object* v_inst_89_, lean_object* v_params_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Server_parseRequestParams___redArg(v_inst_89_, v_params_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_93_; 
v___x_93_ = lean_unsigned_to_nat(0u);
return v___x_93_;
}
else
{
lean_object* v___x_94_; 
v___x_94_ = lean_unsigned_to_nat(1u);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___redArg___boxed(lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_95_);
lean_dec_ref(v_x_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx(lean_object* v_00_u03b1_97_, lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Server_ServerRequestResponse_ctorIdx___redArg(v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorIdx___boxed(lean_object* v_00_u03b1_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Server_ServerRequestResponse_ctorIdx(v_00_u03b1_100_, v_x_101_);
lean_dec_ref(v_x_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___redArg(lean_object* v_t_103_, lean_object* v_k_104_){
_start:
{
if (lean_obj_tag(v_t_103_) == 0)
{
lean_object* v_response_105_; lean_object* v___x_106_; 
v_response_105_ = lean_ctor_get(v_t_103_, 0);
lean_inc(v_response_105_);
lean_dec_ref_known(v_t_103_, 1);
v___x_106_ = lean_apply_1(v_k_104_, v_response_105_);
return v___x_106_;
}
else
{
uint8_t v_code_107_; lean_object* v_message_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_code_107_ = lean_ctor_get_uint8(v_t_103_, sizeof(void*)*1);
v_message_108_ = lean_ctor_get(v_t_103_, 0);
lean_inc_ref(v_message_108_);
lean_dec_ref_known(v_t_103_, 1);
v___x_109_ = lean_box(v_code_107_);
v___x_110_ = lean_apply_2(v_k_104_, v___x_109_, v_message_108_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim(lean_object* v_00_u03b1_111_, lean_object* v_motive_112_, lean_object* v_ctorIdx_113_, lean_object* v_t_114_, lean_object* v_h_115_, lean_object* v_k_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_114_, v_k_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_ctorElim___boxed(lean_object* v_00_u03b1_118_, lean_object* v_motive_119_, lean_object* v_ctorIdx_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_k_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Server_ServerRequestResponse_ctorElim(v_00_u03b1_118_, v_motive_119_, v_ctorIdx_120_, v_t_121_, v_h_122_, v_k_123_);
lean_dec(v_ctorIdx_120_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim___redArg(lean_object* v_t_125_, lean_object* v_success_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_125_, v_success_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_success_elim(lean_object* v_00_u03b1_128_, lean_object* v_motive_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_success_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_130_, v_success_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim___redArg(lean_object* v_t_134_, lean_object* v_failure_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_134_, v_failure_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ServerRequestResponse_failure_elim(lean_object* v_00_u03b1_137_, lean_object* v_motive_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_failure_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Server_ServerRequestResponse_ctorElim___redArg(v_t_139_, v_failure_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse_default(lean_object* v_00_u03b1_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = ((lean_object*)(l_Lean_Server_instInhabitedServerRequestResponse_default___closed__0));
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedServerRequestResponse___closed__0(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Server_instInhabitedServerRequestResponse_default(lean_box(0));
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedServerRequestResponse(lean_object* v_a_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&l_Lean_Server_instInhabitedServerRequestResponse___closed__0, &l_Lean_Server_instInhabitedServerRequestResponse___closed__0_once, _init_l_Lean_Server_instInhabitedServerRequestResponse___closed__0);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg(lean_object* v_act_151_, lean_object* v_rc_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_apply_2(v_act_151_, v_rc_152_, lean_box(0));
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___redArg___boxed(lean_object* v_act_155_, lean_object* v_rc_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Server_RequestM_run___redArg(v_act_155_, v_rc_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run(lean_object* v_00_u03b1_159_, lean_object* v_act_160_, lean_object* v_rc_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_apply_2(v_act_160_, v_rc_161_, lean_box(0));
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_run___boxed(lean_object* v_00_u03b1_164_, lean_object* v_act_165_, lean_object* v_rc_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Server_RequestM_run(v_00_u03b1_164_, v_act_165_, v_rc_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure___redArg(lean_object* v_a_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v_a_169_);
v___x_171_ = lean_task_pure(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestTask_pure(lean_object* v_00_u03b1_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_a_173_);
v___x_175_ = lean_task_pure(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0(lean_object* v_00_u03b1_176_, lean_object* v_x_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_apply_1(v_x_177_, lean_box(0));
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_197_; 
v_a_189_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_197_ == 0)
{
v___x_191_ = v___x_180_;
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_180_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_Server_RequestError_ofIoError(v_a_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___lam__0___boxed(lean_object* v_00_u03b1_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Server_instMonadLiftIORequestM___lam__0(v_00_u03b1_198_, v_x_199_, v___y_200_);
lean_dec_ref(v___y_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(lean_object* v_00_u03b1_205_, lean_object* v_x_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_apply_1(v_x_206_, lean_box(0));
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
v_a_218_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_209_, 1);
v___x_219_ = l_Lean_Server_RequestError_ofException(v_a_218_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0___boxed(lean_object* v_00_u03b1_228_, lean_object* v_x_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Server_instMonadLiftEIOExceptionRequestM___lam__0(v_00_u03b1_228_, v_x_229_, v___y_230_);
lean_dec_ref(v___y_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(lean_object* v_00_u03b1_235_, lean_object* v_x_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_cancelTk_239_; lean_object* v___x_240_; 
v_cancelTk_239_ = lean_ctor_get(v___y_237_, 4);
lean_inc_ref(v_cancelTk_239_);
v___x_240_ = lean_apply_2(v_x_236_, v_cancelTk_239_, lean_box(0));
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_253_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_253_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_253_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_253_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec_ref_known(v_a_241_, 1);
v___x_245_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 1);
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; 
v_a_249_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v_a_241_, 1);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v_a_249_);
v___x_251_ = v___x_243_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_a_254_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_262_ == 0)
{
v___x_256_ = v___x_240_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_240_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = l_Lean_Server_RequestError_ofIoError(v_a_254_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0___boxed(lean_object* v_00_u03b1_263_, lean_object* v_x_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Server_instMonadLiftCancellableMRequestM___lam__0(v_00_u03b1_263_, v_x_264_, v___y_265_);
lean_dec_ref(v___y_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg(lean_object* v_x_270_, lean_object* v_ctx_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_apply_2(v_x_270_, v_ctx_271_, lean_box(0));
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_291_; 
v_a_282_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_291_ == 0)
{
v___x_284_ = v___x_273_;
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_273_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_message_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v_message_286_ = lean_ctor_get(v_a_282_, 0);
lean_inc_ref(v_message_286_);
lean_dec(v_a_282_);
v___x_287_ = lean_mk_io_user_error(v_message_286_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___redArg___boxed(lean_object* v_x_292_, lean_object* v_ctx_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_292_, v_ctx_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO(lean_object* v_00_u03b1_296_, lean_object* v_x_297_, lean_object* v_ctx_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Server_RequestM_runInIO___redArg(v_x_297_, v_ctx_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runInIO___boxed(lean_object* v_00_u03b1_301_, lean_object* v_x_302_, lean_object* v_ctx_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Server_RequestM_runInIO(v_00_u03b1_301_, v_x_302_, v_ctx_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg___lam__0(lean_object* v_toPure_306_, lean_object* v_rc_307_){
_start:
{
lean_object* v_doc_308_; lean_object* v___x_309_; 
v_doc_308_ = lean_ctor_get(v_rc_307_, 1);
lean_inc_ref(v_doc_308_);
lean_dec_ref(v_rc_307_);
v___x_309_ = lean_apply_2(v_toPure_306_, lean_box(0), v_doc_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___redArg(lean_object* v_inst_310_, lean_object* v_inst_311_){
_start:
{
lean_object* v_toApplicative_312_; lean_object* v_toBind_313_; lean_object* v_toPure_314_; lean_object* v___f_315_; lean_object* v___x_316_; 
v_toApplicative_312_ = lean_ctor_get(v_inst_310_, 0);
lean_inc_ref(v_toApplicative_312_);
v_toBind_313_ = lean_ctor_get(v_inst_310_, 1);
lean_inc(v_toBind_313_);
lean_dec_ref(v_inst_310_);
v_toPure_314_ = lean_ctor_get(v_toApplicative_312_, 1);
lean_inc(v_toPure_314_);
lean_dec_ref(v_toApplicative_312_);
v___f_315_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_readDoc___redArg___lam__0), 2, 1);
lean_closure_set(v___f_315_, 0, v_toPure_314_);
v___x_316_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v_inst_311_, v___f_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object* v_m_317_, lean_object* v_inst_318_, lean_object* v_inst_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Server_RequestM_readDoc___redArg(v_inst_318_, v_inst_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0(lean_object* v_t_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
lean_inc_ref(v_a_322_);
v___x_324_ = lean_apply_2(v_t_321_, v_a_322_, lean_box(0));
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed(lean_object* v_t_325_, lean_object* v_a_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Server_RequestM_asTask___redArg___lam__0(v_t_325_, v_a_326_);
lean_dec_ref(v_a_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object* v_t_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_inc_ref(v_a_330_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_asTask___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_332_, 0, v_t_329_);
lean_closure_set(v___f_332_, 1, v_a_330_);
v___x_333_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v___f_332_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___redArg___boxed(lean_object* v_t_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Server_RequestM_asTask___redArg(v_t_335_, v_a_336_);
lean_dec_ref(v_a_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object* v_00_u03b1_339_, lean_object* v_t_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Server_RequestM_asTask___redArg(v_t_340_, v_a_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___boxed(lean_object* v_00_u03b1_344_, lean_object* v_t_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Server_RequestM_asTask(v_00_u03b1_344_, v_t_345_, v_a_346_);
lean_dec_ref(v_a_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg(lean_object* v_t_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; 
lean_inc_ref(v_a_350_);
v___x_352_ = lean_apply_2(v_t_349_, v_a_350_, lean_box(0));
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_362_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_362_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_362_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_362_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_a_353_);
v___x_358_ = lean_task_pure(v___x_357_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_358_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_352_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_352_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___redArg___boxed(lean_object* v_t_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_371_, v_a_372_);
lean_dec_ref(v_a_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask(lean_object* v_00_u03b1_375_, lean_object* v_t_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Server_RequestM_pureTask___redArg(v_t_376_, v_a_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_pureTask___boxed(lean_object* v_00_u03b1_380_, lean_object* v_t_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Server_RequestM_pureTask(v_00_u03b1_380_, v_t_381_, v_a_382_);
lean_dec_ref(v_a_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(lean_object* v_f_385_, lean_object* v_a_386_, lean_object* v_x_387_){
_start:
{
lean_object* v___x_389_; 
lean_inc_ref(v_a_386_);
v___x_389_ = lean_apply_3(v_f_385_, v_x_387_, v_a_386_, lean_box(0));
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed(lean_object* v_f_390_, lean_object* v_a_391_, lean_object* v_x_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0(v_f_390_, v_a_391_, v_x_392_);
lean_dec_ref(v_a_391_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg(lean_object* v_t_395_, lean_object* v_f_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_inc_ref(v_a_397_);
v___f_399_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_399_, 0, v_f_396_);
lean_closure_set(v___f_399_, 1, v_a_397_);
v___x_400_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v___f_399_, v_t_395_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___redArg___boxed(lean_object* v_t_402_, lean_object* v_f_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_402_, v_f_403_, v_a_404_);
lean_dec_ref(v_a_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_t_409_, lean_object* v_f_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_409_, v_f_410_, v_a_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCheap___boxed(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_t_416_, lean_object* v_f_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Server_RequestM_mapTaskCheap(v_00_u03b1_414_, v_00_u03b2_415_, v_t_416_, v_f_417_, v_a_418_);
lean_dec_ref(v_a_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object* v_t_421_, lean_object* v_f_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___f_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_inc_ref(v_a_423_);
v___f_425_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_425_, 0, v_f_422_);
lean_closure_set(v___f_425_, 1, v_a_423_);
v___x_426_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v___f_425_, v_t_421_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg___boxed(lean_object* v_t_428_, lean_object* v_f_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_428_, v_f_429_, v_a_430_);
lean_dec_ref(v_a_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly(lean_object* v_00_u03b1_433_, lean_object* v_00_u03b2_434_, lean_object* v_t_435_, lean_object* v_f_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_435_, v_f_436_, v_a_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTaskCostly___boxed(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_t_442_, lean_object* v_f_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Server_RequestM_mapTaskCostly(v_00_u03b1_440_, v_00_u03b2_441_, v_t_442_, v_f_443_, v_a_444_);
lean_dec_ref(v_a_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(lean_object* v_f_447_, lean_object* v_a_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_451_; 
lean_inc_ref(v_a_448_);
v___x_451_ = lean_apply_3(v_f_447_, v_x_449_, v_a_448_, lean_box(0));
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed(lean_object* v_f_452_, lean_object* v_a_453_, lean_object* v_x_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0(v_f_452_, v_a_453_, v_x_454_);
lean_dec_ref(v_a_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object* v_t_457_, lean_object* v_f_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc_ref(v_a_459_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_461_, 0, v_f_458_);
lean_closure_set(v___f_461_, 1, v_a_459_);
v___x_462_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_457_, v___f_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg___boxed(lean_object* v_t_464_, lean_object* v_f_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_464_, v_f_465_, v_a_466_);
lean_dec_ref(v_a_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_t_471_, lean_object* v_f_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_471_, v_f_472_, v_a_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCheap___boxed(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_t_478_, lean_object* v_f_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Server_RequestM_bindTaskCheap(v_00_u03b1_476_, v_00_u03b2_477_, v_t_478_, v_f_479_, v_a_480_);
lean_dec_ref(v_a_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg(lean_object* v_t_483_, lean_object* v_f_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_inc_ref(v_a_485_);
v___f_487_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTaskCheap___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_487_, 0, v_f_484_);
lean_closure_set(v___f_487_, 1, v_a_485_);
v___x_488_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_483_, v___f_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___redArg___boxed(lean_object* v_t_490_, lean_object* v_f_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_490_, v_f_491_, v_a_492_);
lean_dec_ref(v_a_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_t_497_, lean_object* v_f_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_497_, v_f_498_, v_a_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTaskCostly___boxed(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_t_504_, lean_object* v_f_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Server_RequestM_bindTaskCostly(v_00_u03b1_502_, v_00_u03b2_503_, v_t_504_, v_f_505_, v_a_506_);
lean_dec_ref(v_a_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(lean_object* v_f_509_, lean_object* v_x_510_, lean_object* v___y_511_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v_f_509_);
v_a_513_ = lean_ctor_get(v_x_510_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v_x_510_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v_x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 1);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v_x_510_, 1);
lean_inc_ref(v___y_511_);
v___x_522_ = lean_apply_3(v_f_509_, v_a_521_, v___y_511_, lean_box(0));
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_523_, lean_object* v_x_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0(v_f_523_, v_x_524_, v___y_525_);
lean_dec_ref(v___y_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(lean_object* v_t_528_, lean_object* v_f_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___f_532_; lean_object* v___x_533_; 
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_532_, 0, v_f_529_);
v___x_533_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(v_t_528_, v___f_532_, v_a_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___boxed(lean_object* v_t_534_, lean_object* v_f_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_534_, v_f_535_, v_a_536_);
lean_dec_ref(v_a_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap(lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_t_541_, lean_object* v_f_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Server_RequestM_mapRequestTaskCheap___redArg(v_t_541_, v_f_542_, v_a_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCheap___boxed(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_t_548_, lean_object* v_f_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Server_RequestM_mapRequestTaskCheap(v_00_u03b1_546_, v_00_u03b2_547_, v_t_548_, v_f_549_, v_a_550_);
lean_dec_ref(v_a_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object* v_t_553_, lean_object* v_f_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___f_557_; lean_object* v___x_558_; 
v___f_557_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_557_, 0, v_f_554_);
v___x_558_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_t_553_, v___f_557_, v_a_555_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg___boxed(lean_object* v_t_559_, lean_object* v_f_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_559_, v_f_560_, v_a_561_);
lean_dec_ref(v_a_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_t_566_, lean_object* v_f_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(v_t_566_, v_f_567_, v_a_568_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___boxed(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_t_573_, lean_object* v_f_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Server_RequestM_mapRequestTaskCostly(v_00_u03b1_571_, v_00_u03b2_572_, v_t_573_, v_f_574_, v_a_575_);
lean_dec_ref(v_a_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(lean_object* v_f_578_, lean_object* v_x_579_, lean_object* v___y_580_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_f_578_);
v_a_582_ = lean_ctor_get(v_x_579_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v_x_579_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v_x_579_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set_tag(v___x_584_, 1);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_591_; 
v_a_590_ = lean_ctor_get(v_x_579_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v_x_579_, 1);
lean_inc_ref(v___y_580_);
v___x_591_ = lean_apply_3(v_f_578_, v_a_590_, v___y_580_, lean_box(0));
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed(lean_object* v_f_592_, lean_object* v_x_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0(v_f_592_, v_x_593_, v___y_594_);
lean_dec_ref(v___y_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(lean_object* v_t_597_, lean_object* v_f_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___f_601_; lean_object* v___x_602_; 
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_601_, 0, v_f_598_);
v___x_602_ = l_Lean_Server_RequestM_bindTaskCheap___redArg(v_t_597_, v___f_601_, v_a_599_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___boxed(lean_object* v_t_603_, lean_object* v_f_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_603_, v_f_604_, v_a_605_);
lean_dec_ref(v_a_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_t_610_, lean_object* v_f_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Server_RequestM_bindRequestTaskCheap___redArg(v_t_610_, v_f_611_, v_a_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCheap___boxed(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_t_617_, lean_object* v_f_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Server_RequestM_bindRequestTaskCheap(v_00_u03b1_615_, v_00_u03b2_616_, v_t_617_, v_f_618_, v_a_619_);
lean_dec_ref(v_a_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(lean_object* v_t_622_, lean_object* v_f_623_, lean_object* v_a_624_){
_start:
{
lean_object* v___f_626_; lean_object* v___x_627_; 
v___f_626_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindRequestTaskCheap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_626_, 0, v_f_623_);
v___x_627_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_t_622_, v___f_626_, v_a_624_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___redArg___boxed(lean_object* v_t_628_, lean_object* v_f_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_628_, v_f_629_, v_a_630_);
lean_dec_ref(v_a_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly(lean_object* v_00_u03b1_633_, lean_object* v_00_u03b2_634_, lean_object* v_t_635_, lean_object* v_f_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Server_RequestM_bindRequestTaskCostly___redArg(v_t_635_, v_f_636_, v_a_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindRequestTaskCostly___boxed(lean_object* v_00_u03b1_640_, lean_object* v_00_u03b2_641_, lean_object* v_t_642_, lean_object* v_f_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Server_RequestM_bindRequestTaskCostly(v_00_u03b1_640_, v_00_u03b2_641_, v_t_642_, v_f_643_, v_a_644_);
lean_dec_ref(v_a_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg(lean_object* v_inst_647_, lean_object* v_params_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Server_parseRequestParams___redArg(v_inst_647_, v_params_648_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 1);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_650_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_650_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 0);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___redArg___boxed(lean_object* v_inst_667_, lean_object* v_params_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_667_, v_params_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams(lean_object* v_paramType_671_, lean_object* v_inst_672_, lean_object* v_params_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_672_, v_params_673_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___boxed(lean_object* v_paramType_677_, lean_object* v_inst_678_, lean_object* v_params_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Server_RequestM_parseRequestParams(v_paramType_677_, v_inst_678_, v_params_679_, v_a_680_);
lean_dec_ref(v_a_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object* v_a_683_){
_start:
{
lean_object* v_cancelTk_685_; uint8_t v___x_686_; 
v_cancelTk_685_ = lean_ctor_get(v_a_683_, 4);
v___x_686_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_cancelTk_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_Server_RequestError_requestCancelled));
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_checkCancelled___boxed(lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Server_RequestM_checkCancelled(v_a_691_);
lean_dec_ref(v_a_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0(lean_object* v_inst_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
lean_object* v_response_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_715_; 
v_response_697_ = lean_ctor_get(v_x_696_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_715_ == 0)
{
v___x_699_ = v_x_696_;
v_isShared_700_ = v_isSharedCheck_715_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_response_697_);
lean_dec(v_x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_715_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; 
lean_inc(v_response_697_);
v___x_701_ = lean_apply_1(v_inst_695_, v_response_697_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_del_object(v___x_699_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = 0;
v___x_704_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0___closed__0));
v___x_705_ = l_Lean_Json_compress(v_response_697_);
v___x_706_ = lean_string_append(v___x_704_, v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Server_parseRequestParams___redArg___closed__1));
v___x_708_ = lean_string_append(v___x_706_, v___x_707_);
v___x_709_ = lean_string_append(v___x_708_, v_a_702_);
lean_dec(v_a_702_);
v___x_710_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*1, v___x_703_);
return v___x_710_;
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; 
lean_dec(v_response_697_);
v_a_711_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_701_, 1);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v_a_711_);
v___x_713_ = v___x_699_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
uint8_t v_code_716_; lean_object* v_message_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v_inst_695_);
v_code_716_ = lean_ctor_get_uint8(v_x_696_, sizeof(void*)*1);
v_message_717_ = lean_ctor_get(v_x_696_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v_x_696_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_message_717_);
lean_dec(v_x_696_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_message_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_723_, sizeof(void*)*1, v_code_716_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg(lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_method_727_, lean_object* v_param_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_serverRequestEmitter_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_serverRequestEmitter_731_ = lean_ctor_get(v_a_729_, 5);
v___x_732_ = lean_apply_1(v_inst_725_, v_param_728_);
lean_inc_ref(v_serverRequestEmitter_731_);
v___x_733_ = lean_apply_3(v_serverRequestEmitter_731_, v_method_727_, v___x_732_, lean_box(0));
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___redArg___lam__0), 2, 1);
lean_closure_set(v___f_734_, 0, v_inst_726_);
v___x_735_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_734_, v___x_733_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___redArg___boxed(lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_method_739_, lean_object* v_param_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_737_, v_inst_738_, v_method_739_, v_param_740_, v_a_741_);
lean_dec_ref(v_a_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest(lean_object* v_paramType_744_, lean_object* v_inst_745_, lean_object* v_responseType_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_method_749_, lean_object* v_param_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Server_RequestM_sendServerRequest___redArg(v_inst_745_, v_inst_747_, v_method_749_, v_param_750_, v_a_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___boxed(lean_object* v_paramType_754_, lean_object* v_inst_755_, lean_object* v_responseType_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_method_759_, lean_object* v_param_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Server_RequestM_sendServerRequest(v_paramType_754_, v_inst_755_, v_responseType_756_, v_inst_757_, v_inst_758_, v_method_759_, v_param_760_, v_a_761_);
lean_dec_ref(v_a_761_);
lean_dec(v_inst_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg(lean_object* v_notFoundX_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_a_767_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_x_765_);
lean_dec_ref(v_notFoundX_764_);
v_a_769_ = lean_ctor_get(v_x_766_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_777_ == 0)
{
v___x_771_ = v_x_766_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v_x_766_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = l_Lean_Server_RequestError_ofIoError(v_a_769_);
if (v_isShared_772_ == 0)
{
lean_ctor_set_tag(v___x_771_, 1);
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_object* v_a_778_; 
v_a_778_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v_x_766_, 1);
if (lean_obj_tag(v_a_778_) == 0)
{
lean_object* v___x_779_; 
lean_dec_ref(v_x_765_);
lean_inc_ref(v_a_767_);
v___x_779_ = lean_apply_2(v_notFoundX_764_, v_a_767_, lean_box(0));
return v___x_779_;
}
else
{
lean_object* v_val_780_; lean_object* v___x_781_; 
lean_dec_ref(v_notFoundX_764_);
v_val_780_ = lean_ctor_get(v_a_778_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v_a_778_, 1);
lean_inc_ref(v_a_767_);
v___x_781_ = lean_apply_3(v_x_765_, v_val_780_, v_a_767_, lean_box(0));
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___redArg___boxed(lean_object* v_notFoundX_782_, lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_782_, v_x_783_, v_x_784_, v_a_785_);
lean_dec_ref(v_a_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux(lean_object* v_00_u03b1_788_, lean_object* v_notFoundX_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Server_RequestM_waitFindSnapAux___redArg(v_notFoundX_789_, v_x_790_, v_x_791_, v_a_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_waitFindSnapAux___boxed(lean_object* v_00_u03b1_795_, lean_object* v_notFoundX_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Server_RequestM_waitFindSnapAux(v_00_u03b1_795_, v_notFoundX_796_, v_x_797_, v_x_798_, v_a_799_);
lean_dec_ref(v_a_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object* v_doc_802_, lean_object* v_p_803_, lean_object* v_notFoundX_804_, lean_object* v_x_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_toEditableDocumentCore_808_; lean_object* v_cmdSnaps_809_; lean_object* v_findTask_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_toEditableDocumentCore_808_ = lean_ctor_get(v_doc_802_, 0);
lean_inc_ref(v_toEditableDocumentCore_808_);
lean_dec_ref(v_doc_802_);
v_cmdSnaps_809_ = lean_ctor_get(v_toEditableDocumentCore_808_, 2);
lean_inc(v_cmdSnaps_809_);
lean_dec_ref(v_toEditableDocumentCore_808_);
v_findTask_810_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_803_, v_cmdSnaps_809_);
v___x_811_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_811_, 0, lean_box(0));
lean_closure_set(v___x_811_, 1, v_notFoundX_804_);
lean_closure_set(v___x_811_, 2, v_x_805_);
v___x_812_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_findTask_810_, v___x_811_, v_a_806_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg___boxed(lean_object* v_doc_813_, lean_object* v_p_814_, lean_object* v_notFoundX_815_, lean_object* v_x_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_813_, v_p_814_, v_notFoundX_815_, v_x_816_, v_a_817_);
lean_dec_ref(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object* v_00_u03b2_820_, lean_object* v_doc_821_, lean_object* v_p_822_, lean_object* v_notFoundX_823_, lean_object* v_x_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_doc_821_, v_p_822_, v_notFoundX_823_, v_x_824_, v_a_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___boxed(lean_object* v_00_u03b2_828_, lean_object* v_doc_829_, lean_object* v_p_830_, lean_object* v_notFoundX_831_, lean_object* v_x_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Server_RequestM_withWaitFindSnap(v_00_u03b2_828_, v_doc_829_, v_p_830_, v_notFoundX_831_, v_x_832_, v_a_833_);
lean_dec_ref(v_a_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg(lean_object* v_doc_836_, lean_object* v_p_837_, lean_object* v_notFoundX_838_, lean_object* v_x_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_toEditableDocumentCore_842_; lean_object* v_cmdSnaps_843_; lean_object* v_findTask_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_toEditableDocumentCore_842_ = lean_ctor_get(v_doc_836_, 0);
lean_inc_ref(v_toEditableDocumentCore_842_);
lean_dec_ref(v_doc_836_);
v_cmdSnaps_843_ = lean_ctor_get(v_toEditableDocumentCore_842_, 2);
lean_inc(v_cmdSnaps_843_);
lean_dec_ref(v_toEditableDocumentCore_842_);
v_findTask_844_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_837_, v_cmdSnaps_843_);
v___x_845_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_waitFindSnapAux___boxed), 6, 3);
lean_closure_set(v___x_845_, 0, lean_box(0));
lean_closure_set(v___x_845_, 1, v_notFoundX_838_);
lean_closure_set(v___x_845_, 2, v_x_839_);
v___x_846_ = l_Lean_Server_RequestM_bindTaskCostly___redArg(v_findTask_844_, v___x_845_, v_a_840_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___redArg___boxed(lean_object* v_doc_847_, lean_object* v_p_848_, lean_object* v_notFoundX_849_, lean_object* v_x_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_847_, v_p_848_, v_notFoundX_849_, v_x_850_, v_a_851_);
lean_dec_ref(v_a_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap(lean_object* v_00_u03b2_854_, lean_object* v_doc_855_, lean_object* v_p_856_, lean_object* v_notFoundX_857_, lean_object* v_x_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(v_doc_855_, v_p_856_, v_notFoundX_857_, v_x_858_, v_a_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindWaitFindSnap___boxed(lean_object* v_00_u03b2_862_, lean_object* v_doc_863_, lean_object* v_p_864_, lean_object* v_notFoundX_865_, lean_object* v_x_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Server_RequestM_bindWaitFindSnap(v_00_u03b2_862_, v_doc_863_, v_p_864_, v_notFoundX_865_, v_x_866_, v_a_867_);
lean_dec_ref(v_a_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object* v___y_870_){
_start:
{
lean_object* v_doc_872_; lean_object* v___x_873_; 
v_doc_872_ = lean_ctor_get(v___y_870_, 1);
lean_inc_ref(v_doc_872_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_doc_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0___boxed(lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v___y_874_);
lean_dec_ref(v___y_874_);
return v_res_876_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(lean_object* v___x_877_, lean_object* v_s_878_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_878_);
v___x_880_ = lean_nat_dec_le(v___x_877_, v___x_879_);
lean_dec(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed(lean_object* v___x_881_, lean_object* v_s_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0(v___x_881_, v_s_882_);
lean_dec_ref(v_s_882_);
lean_dec(v___x_881_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(lean_object* v___x_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed(lean_object* v___x_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1(v___x_889_, v___y_890_);
lean_dec_ref(v___y_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(lean_object* v_lspPos_897_, lean_object* v_f_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; lean_object* v_a_902_; lean_object* v_toEditableDocumentCore_903_; lean_object* v_meta_904_; lean_object* v_text_905_; lean_object* v_line_906_; lean_object* v_character_907_; lean_object* v___x_908_; lean_object* v___f_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___x_924_; 
v___x_901_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(v_a_899_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v___x_901_);
v_toEditableDocumentCore_903_ = lean_ctor_get(v_a_902_, 0);
v_meta_904_ = lean_ctor_get(v_toEditableDocumentCore_903_, 0);
v_text_905_ = lean_ctor_get(v_meta_904_, 3);
v_line_906_ = lean_ctor_get(v_lspPos_897_, 0);
lean_inc(v_line_906_);
v_character_907_ = lean_ctor_get(v_lspPos_897_, 1);
lean_inc(v_character_907_);
v___x_908_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_905_, v_lspPos_897_);
v___f_909_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_909_, 0, v___x_908_);
v___x_910_ = 3;
v___x_911_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__0));
v___x_912_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__1));
v___x_913_ = l_Nat_reprFast(v_line_906_);
v___x_914_ = lean_string_append(v___x_912_, v___x_913_);
lean_dec_ref(v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__2));
v___x_916_ = lean_string_append(v___x_914_, v___x_915_);
v___x_917_ = l_Nat_reprFast(v_character_907_);
v___x_918_ = lean_string_append(v___x_916_, v___x_917_);
lean_dec_ref(v___x_917_);
v___x_919_ = ((lean_object*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___closed__3));
v___x_920_ = lean_string_append(v___x_918_, v___x_919_);
v___x_921_ = lean_string_append(v___x_911_, v___x_920_);
lean_dec_ref(v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*1, v___x_910_);
v___f_923_ = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_923_, 0, v___x_922_);
v___x_924_ = l_Lean_Server_RequestM_withWaitFindSnap___redArg(v_a_902_, v___f_909_, v___f_923_, v_f_898_, v_a_899_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg___boxed(lean_object* v_lspPos_925_, lean_object* v_f_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_925_, v_f_926_, v_a_927_);
lean_dec_ref(v_a_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos(lean_object* v_00_u03b1_930_, lean_object* v_lspPos_931_, lean_object* v_f_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos___redArg(v_lspPos_931_, v_f_932_, v_a_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnapAtPos___boxed(lean_object* v_00_u03b1_936_, lean_object* v_lspPos_937_, lean_object* v_f_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Server_RequestM_withWaitFindSnapAtPos(v_00_u03b1_936_, v_lspPos_937_, v_f_938_, v_a_939_);
lean_dec_ref(v_a_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg(lean_object* v_snap_942_, lean_object* v_c_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_doc_946_; lean_object* v_toEditableDocumentCore_947_; lean_object* v_meta_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_doc_946_ = lean_ctor_get(v_a_944_, 1);
v_toEditableDocumentCore_947_ = lean_ctor_get(v_doc_946_, 0);
v_meta_948_ = lean_ctor_get(v_toEditableDocumentCore_947_, 0);
lean_inc_ref(v_a_944_);
v___x_949_ = lean_apply_1(v_c_943_, v_a_944_);
v___x_950_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_942_, v_meta_948_, v___x_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_963_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_963_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_963_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_963_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
if (lean_obj_tag(v_a_951_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; 
v_a_955_ = lean_ctor_get(v_a_951_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v_a_951_, 1);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 1);
lean_ctor_set(v___x_953_, 0, v_a_955_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; 
v_a_959_ = lean_ctor_get(v_a_951_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v_a_951_, 1);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v_a_959_);
v___x_961_ = v___x_953_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_964_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_950_, 1);
v___x_965_ = l_Lean_Server_RequestError_ofException(v_a_964_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 1);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___redArg___boxed(lean_object* v_snap_974_, lean_object* v_c_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_974_, v_c_975_, v_a_976_);
lean_dec_ref(v_a_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM(lean_object* v_00_u03b1_979_, lean_object* v_snap_980_, lean_object* v_c_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Server_RequestM_runCommandElabM___redArg(v_snap_980_, v_c_981_, v_a_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCommandElabM___boxed(lean_object* v_00_u03b1_985_, lean_object* v_snap_986_, lean_object* v_c_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Server_RequestM_runCommandElabM(v_00_u03b1_985_, v_snap_986_, v_c_987_, v_a_988_);
lean_dec_ref(v_a_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg(lean_object* v_snap_991_, lean_object* v_c_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_doc_995_; lean_object* v_toEditableDocumentCore_996_; lean_object* v_meta_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_doc_995_ = lean_ctor_get(v_a_993_, 1);
v_toEditableDocumentCore_996_ = lean_ctor_get(v_doc_995_, 0);
v_meta_997_ = lean_ctor_get(v_toEditableDocumentCore_996_, 0);
lean_inc_ref(v_a_993_);
v___x_998_ = lean_apply_1(v_c_992_, v_a_993_);
v___x_999_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_991_, v_meta_997_, v___x_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1012_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
if (lean_obj_tag(v_a_1000_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; 
v_a_1004_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v_a_1000_, 1);
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 1);
lean_ctor_set(v___x_1002_, 0, v_a_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v_a_1000_, 1);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_a_1008_);
v___x_1010_ = v___x_1002_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1013_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1014_ = l_Lean_Server_RequestError_ofException(v_a_1013_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 1);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___redArg___boxed(lean_object* v_snap_1023_, lean_object* v_c_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1023_, v_c_1024_, v_a_1025_);
lean_dec_ref(v_a_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM(lean_object* v_00_u03b1_1028_, lean_object* v_snap_1029_, lean_object* v_c_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Server_RequestM_runCoreM___redArg(v_snap_1029_, v_c_1030_, v_a_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runCoreM___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_snap_1035_, lean_object* v_c_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Server_RequestM_runCoreM(v_00_u03b1_1034_, v_snap_1035_, v_c_1036_, v_a_1037_);
lean_dec_ref(v_a_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg(lean_object* v_snap_1040_, lean_object* v_c_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_doc_1044_; lean_object* v_toEditableDocumentCore_1045_; lean_object* v_meta_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_doc_1044_ = lean_ctor_get(v_a_1042_, 1);
v_toEditableDocumentCore_1045_ = lean_ctor_get(v_doc_1044_, 0);
v_meta_1046_ = lean_ctor_get(v_toEditableDocumentCore_1045_, 0);
lean_inc_ref(v_a_1042_);
v___x_1047_ = lean_apply_1(v_c_1041_, v_a_1042_);
v___x_1048_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_1040_, v_meta_1046_, v___x_1047_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1061_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1061_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1061_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
if (lean_obj_tag(v_a_1049_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; 
v_a_1053_ = lean_ctor_get(v_a_1049_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v_a_1049_, 1);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
lean_ctor_set(v___x_1051_, 0, v_a_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; 
v_a_1057_ = lean_ctor_get(v_a_1049_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v_a_1049_, 1);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v_a_1057_);
v___x_1059_ = v___x_1051_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1062_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1063_ = l_Lean_Server_RequestError_ofException(v_a_1062_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___redArg___boxed(lean_object* v_snap_1072_, lean_object* v_c_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1072_, v_c_1073_, v_a_1074_);
lean_dec_ref(v_a_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM(lean_object* v_00_u03b1_1077_, lean_object* v_snap_1078_, lean_object* v_c_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Server_RequestM_runTermElabM___redArg(v_snap_1078_, v_c_1079_, v_a_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_runTermElabM___boxed(lean_object* v_00_u03b1_1083_, lean_object* v_snap_1084_, lean_object* v_c_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Server_RequestM_runTermElabM(v_00_u03b1_1083_, v_snap_1084_, v_c_1085_, v_a_1086_);
lean_dec_ref(v_a_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage(lean_object* v_id_1095_, lean_object* v_r_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___y_1100_; 
v___x_1097_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__0));
v___x_1098_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__1));
switch(lean_obj_tag(v_id_1095_))
{
case 0:
{
lean_object* v_s_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_s_1114_ = lean_ctor_get(v_id_1095_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_id_1095_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v_id_1095_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_s_1114_);
lean_dec(v_id_1095_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 3);
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_s_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
v___y_1100_ = v___x_1119_;
goto v___jp_1099_;
}
}
}
case 1:
{
lean_object* v_n_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_n_1122_ = lean_ctor_get(v_id_1095_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_id_1095_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v_id_1095_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_n_1122_);
lean_dec(v_id_1095_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 2);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_n_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v___y_1100_ = v___x_1127_;
goto v___jp_1099_;
}
}
}
default: 
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_box(0);
v___y_1100_ = v___x_1130_;
goto v___jp_1099_;
}
}
v___jp_1099_:
{
lean_object* v_serialized_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_serialized_1101_ = lean_ctor_get(v_r_1096_, 1);
v___x_1102_ = l_Lean_Json_compress(v___y_1100_);
v___x_1103_ = lean_string_append(v___x_1098_, v___x_1102_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__2));
v___x_1105_ = lean_string_append(v___x_1103_, v___x_1104_);
v___x_1106_ = lean_string_append(v___x_1097_, v___x_1105_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__3));
v___x_1108_ = lean_string_append(v___x_1106_, v___x_1107_);
v___x_1109_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__4));
v___x_1110_ = lean_string_append(v___x_1109_, v_serialized_1101_);
v___x_1111_ = lean_string_append(v___x_1108_, v___x_1110_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_Server_SerializedLspResponse_toSerializedMessage___closed__5));
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_SerializedLspResponse_toSerializedMessage___boxed(lean_object* v_id_1131_, lean_object* v_r_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Server_SerializedLspResponse_toSerializedMessage(v_id_1131_, v_r_1132_);
lean_dec_ref(v_r_1132_);
return v_res_1133_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1134_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_);
v___x_1139_ = lean_st_mk_ref(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2____boxed(lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__0(lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_j_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Server_parseRequestParams___redArg(v_inst_1143_, v_j_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v_inst_1144_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
v_a_1155_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1157_ = v___x_1146_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1146_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_apply_1(v_inst_1144_, v_a_1155_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1(lean_object* v_serialize_x3f_1164_, uint8_t v_val_1165_, lean_object* v_inst_1166_, lean_object* v_r_1167_){
_start:
{
if (lean_obj_tag(v_serialize_x3f_1164_) == 1)
{
lean_object* v_val_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec_ref(v_inst_1166_);
v_val_1168_ = lean_ctor_get(v_serialize_x3f_1164_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v_serialize_x3f_1164_, 1);
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_apply_1(v_val_1168_, v_r_1167_);
v___x_1171_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*2, v_val_1165_);
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec(v_serialize_x3f_1164_);
v___x_1172_ = lean_apply_1(v_inst_1166_, v_r_1167_);
lean_inc(v___x_1172_);
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = l_Lean_Json_compress(v___x_1172_);
v___x_1175_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*2, v_val_1165_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed(lean_object* v_serialize_x3f_1176_, lean_object* v_val_1177_, lean_object* v_inst_1178_, lean_object* v_r_1179_){
_start:
{
uint8_t v_val_1655__boxed_1180_; lean_object* v_res_1181_; 
v_val_1655__boxed_1180_ = lean_unbox(v_val_1177_);
v_res_1181_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__1(v_serialize_x3f_1176_, v_val_1655__boxed_1180_, v_inst_1178_, v_r_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2(lean_object* v_inst_1182_, lean_object* v_handler_1183_, lean_object* v___f_1184_, lean_object* v_j_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1182_, v_j_1185_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
lean_inc_ref(v___y_1186_);
v___x_1190_ = lean_apply_3(v_handler_1183_, v_a_1189_, v___y_1186_, lean_box(0));
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1200_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1195_, 0, lean_box(0));
lean_closure_set(v___x_1195_, 1, lean_box(0));
lean_closure_set(v___x_1195_, 2, lean_box(0));
lean_closure_set(v___x_1195_, 3, v___f_1184_);
v___x_1196_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1195_, v_a_1191_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v___f_1184_);
v_a_1201_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1190_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1190_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v___f_1184_);
lean_dec_ref(v_handler_1183_);
v_a_1209_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1188_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1188_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed(lean_object* v_inst_1217_, lean_object* v_handler_1218_, lean_object* v___f_1219_, lean_object* v_j_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_Server_registerLspRequestHandler___redArg___lam__2(v_inst_1217_, v_handler_1218_, v___f_1219_, v_j_1220_, v___y_1221_);
lean_dec_ref(v___y_1221_);
return v_res_1223_;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___f_1228_; 
v___x_1227_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1228_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1228_, 0, v___x_1227_);
return v___f_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg(lean_object* v_method_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_handler_1234_, lean_object* v_serialize_x3f_1235_){
_start:
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Lean_initializing();
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_serialize_x3f_1235_);
lean_dec_ref(v_handler_1234_);
lean_dec_ref(v_inst_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
v___x_1238_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1239_ = lean_string_append(v___x_1238_, v_method_1230_);
lean_dec_ref(v_method_1230_);
v___x_1240_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1241_ = lean_string_append(v___x_1239_, v___x_1240_);
v___x_1242_ = lean_mk_io_user_error(v___x_1241_);
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___f_1247_; uint8_t v___x_1248_; 
v___x_1244_ = l_Lean_Server_requestHandlers;
v___x_1245_ = lean_st_ref_get(v___x_1244_);
v___x_1246_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_1247_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_1230_);
v___x_1248_ = l_Lean_PersistentHashMap_contains___redArg(v___f_1247_, v___x_1246_, v___x_1245_, v_method_1230_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1249_ = lean_st_ref_take(v___x_1244_);
lean_inc_ref(v_inst_1231_);
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1250_, 0, v_inst_1231_);
lean_closure_set(v___f_1250_, 1, v_inst_1232_);
v___x_1251_ = lean_box(v___x_1237_);
v___f_1252_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1252_, 0, v_serialize_x3f_1235_);
lean_closure_set(v___f_1252_, 1, v___x_1251_);
lean_closure_set(v___f_1252_, 2, v_inst_1233_);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1253_, 0, v_inst_1231_);
lean_closure_set(v___f_1253_, 1, v_handler_1234_);
lean_closure_set(v___f_1253_, 2, v___f_1252_);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___f_1250_);
lean_ctor_set(v___x_1254_, 1, v___f_1253_);
v___x_1255_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1247_, v___x_1246_, v___x_1249_, v_method_1230_, v___x_1254_);
v___x_1256_ = lean_st_ref_put(v___x_1244_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec(v_serialize_x3f_1235_);
lean_dec_ref(v_handler_1234_);
lean_dec_ref(v_inst_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
v___x_1258_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__0));
v___x_1259_ = lean_string_append(v___x_1258_, v_method_1230_);
lean_dec_ref(v_method_1230_);
v___x_1260_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_1261_ = lean_string_append(v___x_1259_, v___x_1260_);
v___x_1262_ = lean_mk_io_user_error(v___x_1261_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___redArg___boxed(lean_object* v_method_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_handler_1268_, lean_object* v_serialize_x3f_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1264_, v_inst_1265_, v_inst_1266_, v_inst_1267_, v_handler_1268_, v_serialize_x3f_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* v_method_1272_, lean_object* v_paramType_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_respType_1276_, lean_object* v_inst_1277_, lean_object* v_handler_1278_, lean_object* v_serialize_x3f_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Server_registerLspRequestHandler___redArg(v_method_1272_, v_inst_1274_, v_inst_1275_, v_inst_1277_, v_handler_1278_, v_serialize_x3f_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___boxed(lean_object* v_method_1282_, lean_object* v_paramType_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_respType_1286_, lean_object* v_inst_1287_, lean_object* v_handler_1288_, lean_object* v_serialize_x3f_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Server_registerLspRequestHandler(v_method_1282_, v_paramType_1283_, v_inst_1284_, v_inst_1285_, v_respType_1286_, v_inst_1287_, v_handler_1288_, v_serialize_x3f_1289_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1292_, lean_object* v_vals_1293_, lean_object* v_i_1294_, lean_object* v_k_1295_){
_start:
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = lean_array_get_size(v_keys_1292_);
v___x_1297_ = lean_nat_dec_lt(v_i_1294_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
lean_dec(v_i_1294_);
v___x_1298_ = lean_box(0);
return v___x_1298_;
}
else
{
lean_object* v_k_x27_1299_; uint8_t v___x_1300_; 
v_k_x27_1299_ = lean_array_fget_borrowed(v_keys_1292_, v_i_1294_);
v___x_1300_ = lean_string_dec_eq(v_k_1295_, v_k_x27_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_add(v_i_1294_, v___x_1301_);
lean_dec(v_i_1294_);
v_i_1294_ = v___x_1302_;
goto _start;
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_array_fget_borrowed(v_vals_1293_, v_i_1294_);
lean_dec(v_i_1294_);
lean_inc(v___x_1304_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1306_, lean_object* v_vals_1307_, lean_object* v_i_1308_, lean_object* v_k_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1306_, v_vals_1307_, v_i_1308_, v_k_1309_);
lean_dec_ref(v_k_1309_);
lean_dec_ref(v_vals_1307_);
lean_dec_ref(v_keys_1306_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(lean_object* v_x_1311_, size_t v_x_1312_, lean_object* v_x_1313_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
lean_object* v_es_1314_; lean_object* v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; lean_object* v_j_1318_; lean_object* v___x_1319_; 
v_es_1314_ = lean_ctor_get(v_x_1311_, 0);
v___x_1315_ = lean_box(2);
v___x_1316_ = ((size_t)31ULL);
v___x_1317_ = lean_usize_land(v_x_1312_, v___x_1316_);
v_j_1318_ = lean_usize_to_nat(v___x_1317_);
v___x_1319_ = lean_array_get_borrowed(v___x_1315_, v_es_1314_, v_j_1318_);
lean_dec(v_j_1318_);
switch(lean_obj_tag(v___x_1319_))
{
case 0:
{
lean_object* v_key_1320_; lean_object* v_val_1321_; uint8_t v___x_1322_; 
v_key_1320_ = lean_ctor_get(v___x_1319_, 0);
v_val_1321_ = lean_ctor_get(v___x_1319_, 1);
v___x_1322_ = lean_string_dec_eq(v_x_1313_, v_key_1320_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_box(0);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; 
lean_inc(v_val_1321_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_val_1321_);
return v___x_1324_;
}
}
case 1:
{
lean_object* v_node_1325_; size_t v___x_1326_; size_t v___x_1327_; 
v_node_1325_ = lean_ctor_get(v___x_1319_, 0);
v___x_1326_ = ((size_t)5ULL);
v___x_1327_ = lean_usize_shift_right(v_x_1312_, v___x_1326_);
v_x_1311_ = v_node_1325_;
v_x_1312_ = v___x_1327_;
goto _start;
}
default: 
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
}
}
else
{
lean_object* v_ks_1330_; lean_object* v_vs_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_ks_1330_ = lean_ctor_get(v_x_1311_, 0);
v_vs_1331_ = lean_ctor_get(v_x_1311_, 1);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_ks_1330_, v_vs_1331_, v___x_1332_, v_x_1313_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg___boxed(lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
size_t v_x_263__boxed_1337_; lean_object* v_res_1338_; 
v_x_263__boxed_1337_ = lean_unbox_usize(v_x_1335_);
lean_dec(v_x_1335_);
v_res_1338_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1334_, v_x_263__boxed_1337_, v_x_1336_);
lean_dec_ref(v_x_1336_);
lean_dec_ref(v_x_1334_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
uint64_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_string_hash(v_x_1340_);
v___x_1342_ = lean_uint64_to_usize(v___x_1341_);
v___x_1343_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1339_, v___x_1342_, v_x_1340_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg___boxed(lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1344_, v_x_1345_);
lean_dec_ref(v_x_1345_);
lean_dec_ref(v_x_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* v_method_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = l_Lean_Server_requestHandlers;
v___x_1350_ = lean_st_ref_get(v___x_1349_);
v___x_1351_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_1350_, v_method_1347_);
lean_dec(v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler___boxed(lean_object* v_method_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Server_lookupLspRequestHandler(v_method_1353_);
lean_dec_ref(v_method_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(lean_object* v_00_u03b2_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v_x_1357_, v_x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___boxed(lean_object* v_00_u03b2_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0(v_00_u03b2_1360_, v_x_1361_, v_x_1362_);
lean_dec_ref(v_x_1362_);
lean_dec_ref(v_x_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(lean_object* v_00_u03b2_1364_, lean_object* v_x_1365_, size_t v_x_1366_, lean_object* v_x_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___redArg(v_x_1365_, v_x_1366_, v_x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_){
_start:
{
size_t v_x_341__boxed_1373_; lean_object* v_res_1374_; 
v_x_341__boxed_1373_ = lean_unbox_usize(v_x_1371_);
lean_dec(v_x_1371_);
v_res_1374_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0(v_00_u03b2_1369_, v_x_1370_, v_x_341__boxed_1373_, v_x_1372_);
lean_dec_ref(v_x_1372_);
lean_dec_ref(v_x_1370_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1375_, lean_object* v_keys_1376_, lean_object* v_vals_1377_, lean_object* v_heq_1378_, lean_object* v_i_1379_, lean_object* v_k_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___redArg(v_keys_1376_, v_vals_1377_, v_i_1379_, v_k_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1382_, lean_object* v_keys_1383_, lean_object* v_vals_1384_, lean_object* v_heq_1385_, lean_object* v_i_1386_, lean_object* v_k_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0_spec__0_spec__1(v_00_u03b2_1382_, v_keys_1383_, v_vals_1384_, v_heq_1385_, v_i_1386_, v_k_1387_);
lean_dec_ref(v_k_1387_);
lean_dec_ref(v_vals_1384_);
lean_dec_ref(v_keys_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0(lean_object* v_inst_1392_, lean_object* v_method_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v_response_1396_; 
if (lean_obj_tag(v_x_1394_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_inst_1392_);
v_a_1420_ = lean_ctor_get(v_x_1394_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1394_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v_x_1394_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v_x_1394_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v_response_x3f_1429_; 
v_a_1428_ = lean_ctor_get(v_x_1394_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v_x_1394_, 1);
v_response_x3f_1429_ = lean_ctor_get(v_a_1428_, 0);
if (lean_obj_tag(v_response_x3f_1429_) == 0)
{
lean_object* v_serialized_1430_; lean_object* v___x_1431_; 
v_serialized_1430_ = lean_ctor_get(v_a_1428_, 1);
lean_inc_ref(v_serialized_1430_);
lean_dec(v_a_1428_);
v___x_1431_ = l_Lean_Json_parse(v_serialized_1430_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_inst_1392_);
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1445_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1445_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1436_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__2));
v___x_1437_ = lean_string_append(v___x_1436_, v_method_1393_);
v___x_1438_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1439_ = lean_string_append(v___x_1437_, v___x_1438_);
v___x_1440_ = lean_string_append(v___x_1439_, v_a_1432_);
lean_dec(v_a_1432_);
v___x_1441_ = l_Lean_Server_RequestError_internalError(v___x_1440_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1441_);
v___x_1443_ = v___x_1434_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
lean_object* v_a_1446_; 
v_a_1446_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1431_, 1);
v_response_1396_ = v_a_1446_;
goto v___jp_1395_;
}
}
else
{
lean_object* v_val_1447_; 
lean_inc_ref(v_response_x3f_1429_);
lean_dec(v_a_1428_);
v_val_1447_ = lean_ctor_get(v_response_x3f_1429_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v_response_x3f_1429_, 1);
v_response_1396_ = v_val_1447_;
goto v___jp_1395_;
}
}
v___jp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_apply_1(v_inst_1392_, v_response_1396_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1411_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1402_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__0));
v___x_1403_ = lean_string_append(v___x_1402_, v_method_1393_);
v___x_1404_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___closed__1));
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
v___x_1406_ = lean_string_append(v___x_1405_, v_a_1398_);
lean_dec(v_a_1398_);
v___x_1407_ = l_Lean_Server_RequestError_internalError(v___x_1406_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1407_);
v___x_1409_ = v___x_1400_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1397_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1397_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_1448_, lean_object* v_method_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__0(v_inst_1448_, v_method_1449_, v_x_1450_);
lean_dec_ref(v_method_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1(lean_object* v_inst_1452_, uint8_t v_val_1453_, lean_object* v_r_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1455_ = lean_apply_1(v_inst_1452_, v_r_1454_);
lean_inc(v___x_1455_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
v___x_1457_ = l_Lean_Json_compress(v___x_1455_);
v___x_1458_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*2, v_val_1453_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_1459_, lean_object* v_val_1460_, lean_object* v_r_1461_){
_start:
{
uint8_t v_val_2493__boxed_1462_; lean_object* v_res_1463_; 
v_val_2493__boxed_1462_ = lean_unbox(v_val_1460_);
v_res_1463_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__1(v_inst_1459_, v_val_2493__boxed_1462_, v_r_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2(lean_object* v_handle_1464_, lean_object* v_inst_1465_, lean_object* v___f_1466_, lean_object* v_handler_1467_, lean_object* v___f_1468_, lean_object* v_j_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; 
lean_inc_ref(v___y_1470_);
lean_inc(v_j_1469_);
v___x_1472_ = lean_apply_3(v_handle_1464_, v_j_1469_, v___y_1470_, lean_box(0));
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1465_, v_j_1469_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1466_, v_a_1473_);
lean_inc_ref(v___y_1470_);
v___x_1477_ = lean_apply_4(v_handler_1467_, v_a_1475_, v___x_1476_, v___y_1470_, lean_box(0));
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1487_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1487_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1487_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1482_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_1482_, 0, lean_box(0));
lean_closure_set(v___x_1482_, 1, lean_box(0));
lean_closure_set(v___x_1482_, 2, lean_box(0));
lean_closure_set(v___x_1482_, 3, v___f_1468_);
v___x_1483_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___x_1482_, v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1483_);
v___x_1485_ = v___x_1480_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v___f_1468_);
v_a_1488_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1477_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1477_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1473_);
lean_dec_ref(v___f_1468_);
lean_dec_ref(v_handler_1467_);
lean_dec_ref(v___f_1466_);
v_a_1496_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1474_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1474_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_dec(v_j_1469_);
lean_dec_ref(v___f_1468_);
lean_dec_ref(v_handler_1467_);
lean_dec_ref(v___f_1466_);
lean_dec_ref(v_inst_1465_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed(lean_object* v_handle_1504_, lean_object* v_inst_1505_, lean_object* v___f_1506_, lean_object* v_handler_1507_, lean_object* v___f_1508_, lean_object* v_j_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Server_chainLspRequestHandler___redArg___lam__2(v_handle_1504_, v_inst_1505_, v___f_1506_, v_handler_1507_, v___f_1508_, v_j_1509_, v___y_1510_);
lean_dec_ref(v___y_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg(lean_object* v_method_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_handler_1519_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = l_Lean_initializing();
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec_ref(v_handler_1519_);
lean_dec_ref(v_inst_1518_);
lean_dec_ref(v_inst_1517_);
lean_dec_ref(v_inst_1516_);
v___x_1522_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_1523_ = lean_string_append(v___x_1522_, v_method_1515_);
lean_dec_ref(v_method_1515_);
v___x_1524_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_1525_ = lean_string_append(v___x_1523_, v___x_1524_);
v___x_1526_ = lean_mk_io_user_error(v___x_1525_);
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1564_; 
v___x_1528_ = l_Lean_Server_lookupLspRequestHandler(v_method_1515_);
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1564_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1564_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
if (lean_obj_tag(v_a_1529_) == 1)
{
lean_object* v_val_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_fileSource_1536_; lean_object* v_handle_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1555_; 
v_val_1533_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v_a_1529_, 1);
v___x_1534_ = l_Lean_Server_requestHandlers;
v___x_1535_ = lean_st_ref_take(v___x_1534_);
v_fileSource_1536_ = lean_ctor_get(v_val_1533_, 0);
v_handle_1537_ = lean_ctor_get(v_val_1533_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_val_1533_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1539_ = v_val_1533_;
v_isShared_1540_ = v_isSharedCheck_1555_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_handle_1537_);
lean_inc(v_fileSource_1536_);
lean_dec(v_val_1533_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1555_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___f_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___f_1544_; lean_object* v___f_1545_; lean_object* v___f_1546_; lean_object* v___x_1548_; 
lean_inc_ref(v_method_1515_);
v___f_1541_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1541_, 0, v_inst_1517_);
lean_closure_set(v___f_1541_, 1, v_method_1515_);
v___x_1542_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___x_1543_ = lean_box(v___x_1521_);
v___f_1544_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1544_, 0, v_inst_1518_);
lean_closure_set(v___f_1544_, 1, v___x_1543_);
v___f_1545_ = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1545_, 0, v_handle_1537_);
lean_closure_set(v___f_1545_, 1, v_inst_1516_);
lean_closure_set(v___f_1545_, 2, v___f_1541_);
lean_closure_set(v___f_1545_, 3, v_handler_1519_);
lean_closure_set(v___f_1545_, 4, v___f_1544_);
v___f_1546_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 1, v___f_1545_);
v___x_1548_ = v___x_1539_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_fileSource_1536_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___f_1545_);
v___x_1548_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1549_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1546_, v___x_1542_, v___x_1535_, v_method_1515_, v___x_1548_);
v___x_1550_ = lean_st_ref_put(v___x_1534_, v___x_1549_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1550_);
v___x_1552_ = v___x_1531_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
lean_dec(v_a_1529_);
lean_dec_ref(v_handler_1519_);
lean_dec_ref(v_inst_1518_);
lean_dec_ref(v_inst_1517_);
lean_dec_ref(v_inst_1516_);
v___x_1556_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__0));
v___x_1557_ = lean_string_append(v___x_1556_, v_method_1515_);
lean_dec_ref(v_method_1515_);
v___x_1558_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_1559_ = lean_string_append(v___x_1557_, v___x_1558_);
v___x_1560_ = lean_mk_io_user_error(v___x_1559_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 1);
lean_ctor_set(v___x_1531_, 0, v___x_1560_);
v___x_1562_ = v___x_1531_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___redArg___boxed(lean_object* v_method_1565_, lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_inst_1568_, lean_object* v_handler_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1565_, v_inst_1566_, v_inst_1567_, v_inst_1568_, v_handler_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* v_method_1572_, lean_object* v_paramType_1573_, lean_object* v_inst_1574_, lean_object* v_respType_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_handler_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Server_chainLspRequestHandler___redArg(v_method_1572_, v_inst_1574_, v_inst_1576_, v_inst_1577_, v_handler_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___boxed(lean_object* v_method_1581_, lean_object* v_paramType_1582_, lean_object* v_inst_1583_, lean_object* v_respType_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_handler_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Server_chainLspRequestHandler(v_method_1581_, v_paramType_1582_, v_inst_1583_, v_respType_1584_, v_inst_1585_, v_inst_1586_, v_handler_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx(lean_object* v_x_1590_){
_start:
{
if (lean_obj_tag(v_x_1590_) == 0)
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_unsigned_to_nat(0u);
return v___x_1591_;
}
else
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_unsigned_to_nat(1u);
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorIdx___boxed(lean_object* v_x_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Server_RequestHandlerCompleteness_ctorIdx(v_x_1593_);
lean_dec(v_x_1593_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(lean_object* v_t_1595_, lean_object* v_k_1596_){
_start:
{
if (lean_obj_tag(v_t_1595_) == 0)
{
return v_k_1596_;
}
else
{
lean_object* v_refreshMethod_1597_; lean_object* v_refreshIntervalMs_1598_; lean_object* v___x_1599_; 
v_refreshMethod_1597_ = lean_ctor_get(v_t_1595_, 0);
lean_inc_ref(v_refreshMethod_1597_);
v_refreshIntervalMs_1598_ = lean_ctor_get(v_t_1595_, 1);
lean_inc(v_refreshIntervalMs_1598_);
lean_dec_ref_known(v_t_1595_, 2);
v___x_1599_ = lean_apply_2(v_k_1596_, v_refreshMethod_1597_, v_refreshIntervalMs_1598_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim(lean_object* v_motive_1600_, lean_object* v_ctorIdx_1601_, lean_object* v_t_1602_, lean_object* v_h_1603_, lean_object* v_k_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1602_, v_k_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_ctorElim___boxed(lean_object* v_motive_1606_, lean_object* v_ctorIdx_1607_, lean_object* v_t_1608_, lean_object* v_h_1609_, lean_object* v_k_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim(v_motive_1606_, v_ctorIdx_1607_, v_t_1608_, v_h_1609_, v_k_1610_);
lean_dec(v_ctorIdx_1607_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim___redArg(lean_object* v_t_1612_, lean_object* v_complete_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1612_, v_complete_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_complete_elim(lean_object* v_motive_1615_, lean_object* v_t_1616_, lean_object* v_h_1617_, lean_object* v_complete_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1616_, v_complete_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim___redArg(lean_object* v_t_1620_, lean_object* v_partial_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1620_, v_partial_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestHandlerCompleteness_partial_elim(lean_object* v_motive_1623_, lean_object* v_t_1624_, lean_object* v_h_1625_, lean_object* v_partial_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Server_RequestHandlerCompleteness_ctorElim___redArg(v_t_1624_, v_partial_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1628_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_, &l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2__once, _init_l___private_Lean_Server_Requests_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_);
v___x_1633_ = lean_st_mk_ref(v___x_1632_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2____boxed(lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(lean_object* v_method_1638_, lean_object* v_state_1639_, lean_object* v_inst_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_1639_, v_inst_1640_);
if (lean_obj_tag(v___x_1642_) == 1)
{
lean_object* v_val_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_val_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_val_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 0);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec(v___x_1642_);
v___x_1651_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_1652_ = lean_string_append(v___x_1651_, v_method_1638_);
v___x_1653_ = l_Lean_Server_RequestError_internalError(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___boxed(lean_object* v_method_1655_, lean_object* v_state_1656_, lean_object* v_inst_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1655_, v_state_1656_, v_inst_1657_);
lean_dec(v_inst_1657_);
lean_dec(v_state_1656_);
lean_dec_ref(v_method_1655_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object* v_method_1660_, lean_object* v_state_1661_, lean_object* v_stateType_1662_, lean_object* v_inst_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1660_, v_state_1661_, v_inst_1663_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___boxed(lean_object* v_method_1667_, lean_object* v_state_1668_, lean_object* v_stateType_1669_, lean_object* v_inst_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_1667_, v_state_1668_, v_stateType_1669_, v_inst_1670_, v_a_1671_);
lean_dec_ref(v_a_1671_);
lean_dec(v_inst_1670_);
lean_dec(v_state_1668_);
lean_dec_ref(v_method_1667_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(lean_object* v_method_1674_, lean_object* v_state_1675_, lean_object* v_inst_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_state_1675_, v_inst_1676_);
if (lean_obj_tag(v___x_1678_) == 1)
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_val_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_val_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec(v___x_1678_);
v___x_1687_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg___closed__0));
v___x_1688_ = lean_string_append(v___x_1687_, v_method_1674_);
v___x_1689_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg___boxed(lean_object* v_method_1691_, lean_object* v_state_1692_, lean_object* v_inst_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1691_, v_state_1692_, v_inst_1693_);
lean_dec(v_inst_1693_);
lean_dec(v_state_1692_);
lean_dec_ref(v_method_1691_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(lean_object* v_method_1696_, lean_object* v_state_1697_, lean_object* v_stateType_1698_, lean_object* v_inst_1699_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_1696_, v_state_1697_, v_inst_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___boxed(lean_object* v_method_1702_, lean_object* v_state_1703_, lean_object* v_stateType_1704_, lean_object* v_inst_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21(v_method_1702_, v_state_1703_, v_stateType_1704_, v_inst_1705_);
lean_dec(v_inst_1705_);
lean_dec(v_state_1703_);
lean_dec_ref(v_method_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_1708_, lean_object* v_method_1709_, lean_object* v_inst_1710_, lean_object* v_handler_1711_, lean_object* v_inst_1712_, lean_object* v_param_1713_, lean_object* v_state_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Server_RequestM_parseRequestParams___redArg(v_inst_1708_, v_param_1713_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1709_, v_state_1714_, v_inst_1710_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
lean_inc_ref(v___y_1715_);
v___x_1721_ = lean_apply_4(v_handler_1711_, v_a_1718_, v_a_1720_, v___y_1715_, lean_box(0));
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1745_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1745_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1745_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_fst_1726_; lean_object* v_snd_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1744_; 
v_fst_1726_ = lean_ctor_get(v_a_1722_, 0);
v_snd_1727_ = lean_ctor_get(v_a_1722_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1722_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1729_ = v_a_1722_;
v_isShared_1730_ = v_isSharedCheck_1744_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_snd_1727_);
lean_inc(v_fst_1726_);
lean_dec(v_a_1722_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1744_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_response_1731_; uint8_t v_isComplete_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v_response_1731_ = lean_ctor_get(v_fst_1726_, 0);
lean_inc(v_response_1731_);
v_isComplete_1732_ = lean_ctor_get_uint8(v_fst_1726_, sizeof(void*)*1);
lean_dec(v_fst_1726_);
v___x_1733_ = lean_apply_1(v_inst_1712_, v_response_1731_);
lean_inc(v___x_1733_);
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
v___x_1735_ = l_Lean_Json_compress(v___x_1733_);
v___x_1736_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*2, v_isComplete_1732_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v_inst_1710_);
v___x_1738_ = v___x_1729_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_inst_1710_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_snd_1727_);
v___x_1738_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1736_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1739_);
v___x_1741_ = v___x_1724_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v_inst_1712_);
lean_dec(v_inst_1710_);
v_a_1746_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1721_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1721_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_a_1718_);
lean_dec_ref(v_inst_1712_);
lean_dec_ref(v_handler_1711_);
lean_dec(v_inst_1710_);
v_a_1754_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1719_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1719_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v_inst_1712_);
lean_dec_ref(v_handler_1711_);
lean_dec(v_inst_1710_);
v_a_1762_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1717_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1717_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_1770_, lean_object* v_method_1771_, lean_object* v_inst_1772_, lean_object* v_handler_1773_, lean_object* v_inst_1774_, lean_object* v_param_1775_, lean_object* v_state_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1(v_inst_1770_, v_method_1771_, v_inst_1772_, v_handler_1773_, v_inst_1774_, v_param_1775_, v_state_1776_, v___y_1777_);
lean_dec_ref(v___y_1777_);
lean_dec(v_state_1776_);
lean_dec_ref(v_method_1771_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(lean_object* v_method_1780_, lean_object* v_inst_1781_, lean_object* v_onDidChange_1782_, lean_object* v_param_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_1780_, v___y_1784_, v_inst_1781_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
lean_inc_ref(v___y_1785_);
v___x_1789_ = lean_apply_4(v_onDidChange_1782_, v_param_1783_, v_a_1788_, v___y_1785_, lean_box(0));
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1808_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1808_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1808_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_snd_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1806_; 
v_snd_1794_ = lean_ctor_get(v_a_1790_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1790_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_a_1790_, 0);
lean_dec(v_unused_1807_);
v___x_1796_ = v_a_1790_;
v_isShared_1797_ = v_isSharedCheck_1806_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_snd_1794_);
lean_dec(v_a_1790_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1806_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v_inst_1781_);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_inst_1781_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_snd_1794_);
v___x_1799_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1799_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1801_);
v___x_1803_ = v___x_1792_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_inst_1781_);
v_a_1809_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1789_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1789_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v_param_1783_);
lean_dec_ref(v_onDidChange_1782_);
lean_dec(v_inst_1781_);
v_a_1817_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1787_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1787_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_method_1825_, lean_object* v_inst_1826_, lean_object* v_onDidChange_1827_, lean_object* v_param_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0(v_method_1825_, v_inst_1826_, v_onDidChange_1827_, v_param_1828_, v___y_1829_, v___y_1830_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v_method_1825_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(lean_object* v___x_1833_, lean_object* v_x_1834_){
_start:
{
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2___boxed(lean_object* v___x_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__2(v___x_1835_, v_x_1836_);
lean_dec_ref(v_x_1836_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(lean_object* v___x_1838_, lean_object* v_x_1839_){
_start:
{
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3___boxed(lean_object* v___x_1840_, lean_object* v_x_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__3(v___x_1840_, v_x_1841_);
lean_dec_ref(v_x_1841_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(lean_object* v_val_1843_, lean_object* v___f_1844_, lean_object* v_param_1845_, lean_object* v_x_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_st_ref_get(v_val_1843_);
lean_inc_ref(v___y_1847_);
v___x_1850_ = lean_apply_4(v___f_1844_, v_param_1845_, v___x_1849_, v___y_1847_, lean_box(0));
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1861_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1861_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1861_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_fst_1855_; lean_object* v_snd_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v_fst_1855_ = lean_ctor_get(v_a_1851_, 0);
lean_inc(v_fst_1855_);
v_snd_1856_ = lean_ctor_get(v_a_1851_, 1);
lean_inc(v_snd_1856_);
lean_dec(v_a_1851_);
v___x_1857_ = lean_st_ref_swap(v_val_1843_, v_snd_1856_);
lean_dec(v___x_1857_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_fst_1855_);
v___x_1859_ = v___x_1853_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_fst_1855_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1850_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1850_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed(lean_object* v_val_1870_, lean_object* v___f_1871_, lean_object* v_param_1872_, lean_object* v_x_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4(v_val_1870_, v___f_1871_, v_param_1872_, v_x_1873_, v___y_1874_);
lean_dec_ref(v___y_1874_);
lean_dec(v_val_1870_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(lean_object* v___f_1877_, lean_object* v___f_1878_, lean_object* v_lastTask_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1893_; 
v___x_1883_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_1879_, v___f_1877_, v___y_1881_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_inc(v_a_1884_);
v___x_1888_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1878_, v_a_1884_);
v___x_1889_ = lean_st_ref_swap(v___y_1880_, v___x_1888_);
lean_dec(v___x_1889_);
if (v_isShared_1887_ == 0)
{
v___x_1891_ = v___x_1886_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1884_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed(lean_object* v___f_1894_, lean_object* v___f_1895_, lean_object* v_lastTask_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5(v___f_1894_, v___f_1895_, v_lastTask_1896_, v___y_1897_, v___y_1898_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(lean_object* v_val_1901_, lean_object* v___f_1902_, lean_object* v___f_1903_, lean_object* v___f_1904_, lean_object* v___x_1905_, lean_object* v___f_1906_, lean_object* v___f_1907_, lean_object* v_val_1908_, lean_object* v_param_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___f_1912_; lean_object* v___f_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_6577__overap_1916_; lean_object* v___x_1917_; 
v___f_1912_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1912_, 0, v_val_1901_);
lean_closure_set(v___f_1912_, 1, v___f_1902_);
lean_closure_set(v___f_1912_, 2, v_param_1909_);
v___f_1913_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__5___boxed), 6, 2);
lean_closure_set(v___f_1913_, 0, v___f_1912_);
lean_closure_set(v___f_1913_, 1, v___f_1903_);
v___x_1914_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1914_, 0, lean_box(0));
lean_closure_set(v___x_1914_, 1, lean_box(0));
lean_closure_set(v___x_1914_, 2, lean_box(0));
lean_closure_set(v___x_1914_, 3, v___f_1904_);
lean_inc_ref(v___x_1905_);
v___x_1915_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1915_, 0, lean_box(0));
lean_closure_set(v___x_1915_, 1, lean_box(0));
lean_closure_set(v___x_1915_, 2, v___x_1905_);
lean_closure_set(v___x_1915_, 3, lean_box(0));
lean_closure_set(v___x_1915_, 4, lean_box(0));
lean_closure_set(v___x_1915_, 5, v___x_1914_);
lean_closure_set(v___x_1915_, 6, v___f_1913_);
v___x_6577__overap_1916_ = l_Std_Mutex_atomically___redArg(v___x_1905_, v___f_1906_, v___f_1907_, v_val_1908_, v___x_1915_);
lean_inc_ref(v___y_1910_);
v___x_1917_ = lean_apply_2(v___x_6577__overap_1916_, v___y_1910_, lean_box(0));
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed(lean_object* v_val_1918_, lean_object* v___f_1919_, lean_object* v___f_1920_, lean_object* v___f_1921_, lean_object* v___x_1922_, lean_object* v___f_1923_, lean_object* v___f_1924_, lean_object* v_val_1925_, lean_object* v_param_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6(v_val_1918_, v___f_1919_, v___f_1920_, v___f_1921_, v___x_1922_, v___f_1923_, v___f_1924_, v_val_1925_, v_param_1926_, v___y_1927_);
lean_dec_ref(v___y_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(lean_object* v_val_1930_, lean_object* v___f_1931_, lean_object* v_param_1932_, lean_object* v___x_1933_, lean_object* v_x_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_st_ref_get(v_val_1930_);
lean_inc_ref(v___y_1935_);
v___x_1938_ = lean_apply_4(v___f_1931_, v_param_1932_, v___x_1937_, v___y_1935_, lean_box(0));
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1948_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v_snd_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v_snd_1943_ = lean_ctor_get(v_a_1939_, 1);
lean_inc(v_snd_1943_);
lean_dec(v_a_1939_);
v___x_1944_ = lean_st_ref_swap(v_val_1930_, v_snd_1943_);
lean_dec(v___x_1944_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1933_);
v___x_1946_ = v___x_1941_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1933_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_a_1949_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1938_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1938_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed(lean_object* v_val_1957_, lean_object* v___f_1958_, lean_object* v_param_1959_, lean_object* v___x_1960_, lean_object* v_x_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7(v_val_1957_, v___f_1958_, v_param_1959_, v___x_1960_, v_x_1961_, v___y_1962_);
lean_dec_ref(v___y_1962_);
lean_dec(v_val_1957_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(lean_object* v___f_1965_, lean_object* v___f_1966_, lean_object* v___x_1967_, lean_object* v_lastTask_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1982_; 
v___x_1972_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v_lastTask_1968_, v___f_1965_, v___y_1970_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1982_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1982_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1977_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1966_, v_a_1973_);
v___x_1978_ = lean_st_ref_swap(v___y_1969_, v___x_1977_);
lean_dec(v___x_1978_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1967_);
v___x_1980_ = v___x_1975_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1967_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed(lean_object* v___f_1983_, lean_object* v___f_1984_, lean_object* v___x_1985_, lean_object* v_lastTask_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8(v___f_1983_, v___f_1984_, v___x_1985_, v_lastTask_1986_, v___y_1987_, v___y_1988_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(lean_object* v_val_1991_, lean_object* v___f_1992_, lean_object* v___x_1993_, lean_object* v___f_1994_, lean_object* v___f_1995_, lean_object* v___x_1996_, lean_object* v___f_1997_, lean_object* v___f_1998_, lean_object* v_val_1999_, lean_object* v_param_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___f_2003_; lean_object* v___f_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_6631__overap_2007_; lean_object* v___x_2008_; 
v___f_2003_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2003_, 0, v_val_1991_);
lean_closure_set(v___f_2003_, 1, v___f_1992_);
lean_closure_set(v___f_2003_, 2, v_param_2000_);
lean_closure_set(v___f_2003_, 3, v___x_1993_);
v___f_2004_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__8___boxed), 7, 3);
lean_closure_set(v___f_2004_, 0, v___f_2003_);
lean_closure_set(v___f_2004_, 1, v___f_1994_);
lean_closure_set(v___f_2004_, 2, v___x_1993_);
v___x_2005_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_2005_, 0, lean_box(0));
lean_closure_set(v___x_2005_, 1, lean_box(0));
lean_closure_set(v___x_2005_, 2, lean_box(0));
lean_closure_set(v___x_2005_, 3, v___f_1995_);
lean_inc_ref(v___x_1996_);
v___x_2006_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2006_, 0, lean_box(0));
lean_closure_set(v___x_2006_, 1, lean_box(0));
lean_closure_set(v___x_2006_, 2, v___x_1996_);
lean_closure_set(v___x_2006_, 3, lean_box(0));
lean_closure_set(v___x_2006_, 4, lean_box(0));
lean_closure_set(v___x_2006_, 5, v___x_2005_);
lean_closure_set(v___x_2006_, 6, v___f_2004_);
v___x_6631__overap_2007_ = l_Std_Mutex_atomically___redArg(v___x_1996_, v___f_1997_, v___f_1998_, v_val_1999_, v___x_2006_);
lean_inc_ref(v___y_2001_);
v___x_2008_ = lean_apply_2(v___x_6631__overap_2007_, v___y_2001_, lean_box(0));
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed(lean_object* v_val_2009_, lean_object* v___f_2010_, lean_object* v___x_2011_, lean_object* v___f_2012_, lean_object* v___f_2013_, lean_object* v___x_2014_, lean_object* v___f_2015_, lean_object* v___f_2016_, lean_object* v_val_2017_, lean_object* v_param_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9(v_val_2009_, v___f_2010_, v___x_2011_, v___f_2012_, v___f_2013_, v___x_2014_, v___f_2015_, v___f_2016_, v_val_2017_, v_param_2018_, v___y_2019_);
lean_dec_ref(v___y_2019_);
return v_res_2021_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0(void){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_instMonadEIO(lean_box(0));
return v___x_2022_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__0);
v___x_2024_ = l_ReaderT_instMonad___redArg(v___x_2023_);
return v___x_2024_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_box(0);
v___x_2027_ = lean_task_pure(v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(lean_object* v_method_2053_, lean_object* v_completeness_2054_, lean_object* v_inst_2055_, lean_object* v_inst_2056_, lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_initState_2059_, lean_object* v_handler_2060_, lean_object* v_onDidChange_2061_){
_start:
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__1);
v___x_2064_ = l_Lean_initializing();
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref(v_onDidChange_2061_);
lean_dec_ref(v_handler_2060_);
lean_dec(v_initState_2059_);
lean_dec(v_inst_2058_);
lean_dec_ref(v_inst_2057_);
lean_dec_ref(v_inst_2056_);
lean_dec_ref(v_inst_2055_);
lean_dec(v_completeness_2054_);
v___x_2065_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2));
v___x_2066_ = lean_string_append(v___x_2065_, v_method_2053_);
lean_dec_ref(v_method_2053_);
v___x_2067_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_2068_ = lean_string_append(v___x_2066_, v___x_2067_);
v___x_2069_ = lean_mk_io_user_error(v___x_2068_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___f_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__3);
v___x_2073_ = l_Std_Mutex_new___redArg(v___x_2072_);
lean_inc_n(v_inst_2058_, 2);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_inst_2058_);
lean_ctor_set(v___x_2074_, 1, v_initState_2059_);
lean_inc_ref(v___x_2074_);
v___x_2075_ = lean_st_mk_ref(v___x_2074_);
v___x_2076_ = l_Lean_Server_statefulRequestHandlers;
v___x_2077_ = lean_st_ref_take(v___x_2076_);
v___f_2078_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__7));
lean_inc_ref(v_inst_2055_);
v___f_2079_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2079_, 0, v_inst_2055_);
lean_closure_set(v___f_2079_, 1, v_inst_2056_);
lean_inc_ref_n(v_method_2053_, 2);
v___f_2080_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__1___boxed), 9, 5);
lean_closure_set(v___f_2080_, 0, v_inst_2055_);
lean_closure_set(v___f_2080_, 1, v_method_2053_);
lean_closure_set(v___f_2080_, 2, v_inst_2058_);
lean_closure_set(v___f_2080_, 3, v_handler_2060_);
lean_closure_set(v___f_2080_, 4, v_inst_2057_);
v___f_2081_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_2081_, 0, v_method_2053_);
lean_closure_set(v___f_2081_, 1, v_inst_2058_);
lean_closure_set(v___f_2081_, 2, v_onDidChange_2061_);
v___f_2082_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__9));
v___f_2083_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__13));
v___x_2084_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2085_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__14));
v___f_2086_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__15));
lean_inc_ref_n(v___x_2073_, 2);
lean_inc_ref(v___f_2080_);
lean_inc_n(v___x_2075_, 2);
v___f_2087_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__6___boxed), 11, 8);
lean_closure_set(v___f_2087_, 0, v___x_2075_);
lean_closure_set(v___f_2087_, 1, v___f_2080_);
lean_closure_set(v___f_2087_, 2, v___f_2085_);
lean_closure_set(v___f_2087_, 3, v___f_2083_);
lean_closure_set(v___f_2087_, 4, v___x_2063_);
lean_closure_set(v___f_2087_, 5, v___f_2078_);
lean_closure_set(v___f_2087_, 6, v___f_2082_);
lean_closure_set(v___f_2087_, 7, v___x_2073_);
lean_inc_ref(v___f_2081_);
v___f_2088_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___lam__9___boxed), 12, 9);
lean_closure_set(v___f_2088_, 0, v___x_2075_);
lean_closure_set(v___f_2088_, 1, v___f_2081_);
lean_closure_set(v___f_2088_, 2, v___x_2071_);
lean_closure_set(v___f_2088_, 3, v___f_2086_);
lean_closure_set(v___f_2088_, 4, v___f_2083_);
lean_closure_set(v___f_2088_, 5, v___x_2063_);
lean_closure_set(v___f_2088_, 6, v___f_2078_);
lean_closure_set(v___f_2088_, 7, v___f_2082_);
lean_closure_set(v___f_2088_, 8, v___x_2073_);
v___f_2089_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
v___x_2090_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2090_, 0, v___f_2079_);
lean_ctor_set(v___x_2090_, 1, v___f_2080_);
lean_ctor_set(v___x_2090_, 2, v___f_2087_);
lean_ctor_set(v___x_2090_, 3, v___f_2081_);
lean_ctor_set(v___x_2090_, 4, v___f_2088_);
lean_ctor_set(v___x_2090_, 5, v___x_2073_);
lean_ctor_set(v___x_2090_, 6, v___x_2074_);
lean_ctor_set(v___x_2090_, 7, v___x_2075_);
lean_ctor_set(v___x_2090_, 8, v_completeness_2054_);
v___x_2091_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2089_, v___x_2084_, v___x_2077_, v_method_2053_, v___x_2090_);
v___x_2092_ = lean_st_ref_put(v___x_2076_, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2094_, lean_object* v_completeness_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_initState_2100_, lean_object* v_handler_2101_, lean_object* v_onDidChange_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2094_, v_completeness_2095_, v_inst_2096_, v_inst_2097_, v_inst_2098_, v_inst_2099_, v_initState_2100_, v_handler_2101_, v_onDidChange_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(lean_object* v_method_2105_, lean_object* v_completeness_2106_, lean_object* v_paramType_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_respType_2110_, lean_object* v_inst_2111_, lean_object* v_stateType_2112_, lean_object* v_inst_2113_, lean_object* v_initState_2114_, lean_object* v_handler_2115_, lean_object* v_onDidChange_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2105_, v_completeness_2106_, v_inst_2108_, v_inst_2109_, v_inst_2111_, v_inst_2113_, v_initState_2114_, v_handler_2115_, v_onDidChange_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___boxed(lean_object* v_method_2119_, lean_object* v_completeness_2120_, lean_object* v_paramType_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_respType_2124_, lean_object* v_inst_2125_, lean_object* v_stateType_2126_, lean_object* v_inst_2127_, lean_object* v_initState_2128_, lean_object* v_handler_2129_, lean_object* v_onDidChange_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler(v_method_2119_, v_completeness_2120_, v_paramType_2121_, v_inst_2122_, v_inst_2123_, v_respType_2124_, v_inst_2125_, v_stateType_2126_, v_inst_2127_, v_initState_2128_, v_handler_2129_, v_onDidChange_2130_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(lean_object* v_method_2133_, lean_object* v_completeness_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_initState_2139_, lean_object* v_handler_2140_, lean_object* v_onDidChange_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; uint8_t v___x_2147_; 
v___x_2143_ = l_Lean_Server_requestHandlers;
v___x_2144_ = lean_st_ref_get(v___x_2143_);
v___x_2145_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__2));
v___f_2146_ = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___redArg___closed__3, &l_Lean_Server_registerLspRequestHandler___redArg___closed__3_once, _init_l_Lean_Server_registerLspRequestHandler___redArg___closed__3);
lean_inc_ref(v_method_2133_);
v___x_2147_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2146_, v___x_2145_, v___x_2144_, v_method_2133_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; 
v___x_2148_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2133_, v_completeness_2134_, v_inst_2135_, v_inst_2136_, v_inst_2137_, v_inst_2138_, v_initState_2139_, v_handler_2140_, v_onDidChange_2141_);
return v___x_2148_;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v_onDidChange_2141_);
lean_dec_ref(v_handler_2140_);
lean_dec(v_initState_2139_);
lean_dec(v_inst_2138_);
lean_dec_ref(v_inst_2137_);
lean_dec_ref(v_inst_2136_);
lean_dec_ref(v_inst_2135_);
lean_dec(v_completeness_2134_);
v___x_2149_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg___closed__2));
v___x_2150_ = lean_string_append(v___x_2149_, v_method_2133_);
lean_dec_ref(v_method_2133_);
v___x_2151_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__4));
v___x_2152_ = lean_string_append(v___x_2150_, v___x_2151_);
v___x_2153_ = lean_mk_io_user_error(v___x_2152_);
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2155_, lean_object* v_completeness_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_initState_2161_, lean_object* v_handler_2162_, lean_object* v_onDidChange_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2155_, v_completeness_2156_, v_inst_2157_, v_inst_2158_, v_inst_2159_, v_inst_2160_, v_initState_2161_, v_handler_2162_, v_onDidChange_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(lean_object* v_method_2166_, lean_object* v_completeness_2167_, lean_object* v_paramType_2168_, lean_object* v_inst_2169_, lean_object* v_inst_2170_, lean_object* v_respType_2171_, lean_object* v_inst_2172_, lean_object* v_stateType_2173_, lean_object* v_inst_2174_, lean_object* v_initState_2175_, lean_object* v_handler_2176_, lean_object* v_onDidChange_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2166_, v_completeness_2167_, v_inst_2169_, v_inst_2170_, v_inst_2172_, v_inst_2174_, v_initState_2175_, v_handler_2176_, v_onDidChange_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___boxed(lean_object* v_method_2180_, lean_object* v_completeness_2181_, lean_object* v_paramType_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_, lean_object* v_respType_2185_, lean_object* v_inst_2186_, lean_object* v_stateType_2187_, lean_object* v_inst_2188_, lean_object* v_initState_2189_, lean_object* v_handler_2190_, lean_object* v_onDidChange_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler(v_method_2180_, v_completeness_2181_, v_paramType_2182_, v_inst_2183_, v_inst_2184_, v_respType_2185_, v_inst_2186_, v_stateType_2187_, v_inst_2188_, v_initState_2189_, v_handler_2190_, v_onDidChange_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(lean_object* v_handler_2194_, lean_object* v_p_2195_, lean_object* v_s_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
lean_inc_ref(v___y_2197_);
v___x_2199_ = lean_apply_4(v_handler_2194_, v_p_2195_, v_s_2196_, v___y_2197_, lean_box(0));
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2218_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2218_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2218_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_fst_2204_; lean_object* v_snd_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2217_; 
v_fst_2204_ = lean_ctor_get(v_a_2200_, 0);
v_snd_2205_ = lean_ctor_get(v_a_2200_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_a_2200_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2207_ = v_a_2200_;
v_isShared_2208_ = v_isSharedCheck_2217_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_snd_2205_);
lean_inc(v_fst_2204_);
lean_dec(v_a_2200_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2217_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2209_ = 1;
v___x_2210_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2210_, 0, v_fst_2204_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*1, v___x_2209_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2210_);
v___x_2212_ = v___x_2207_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_snd_2205_);
v___x_2212_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2214_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2212_);
v___x_2214_ = v___x_2202_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_a_2219_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2199_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2199_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_handler_2227_, lean_object* v_p_2228_, lean_object* v_s_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0(v_handler_2227_, v_p_2228_, v_s_2229_, v___y_2230_);
lean_dec_ref(v___y_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(lean_object* v_method_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_initState_2238_, lean_object* v_handler_2239_, lean_object* v_onDidChange_2240_){
_start:
{
lean_object* v_handler_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_handler_2242_ = lean_alloc_closure((void*)(l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v_handler_2242_, 0, v_handler_2239_);
v___x_2243_ = lean_box(0);
v___x_2244_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2233_, v___x_2243_, v_inst_2234_, v_inst_2235_, v_inst_2236_, v_inst_2237_, v_initState_2238_, v_handler_2242_, v_onDidChange_2240_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_initState_2250_, lean_object* v_handler_2251_, lean_object* v_onDidChange_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2245_, v_inst_2246_, v_inst_2247_, v_inst_2248_, v_inst_2249_, v_initState_2250_, v_handler_2251_, v_onDidChange_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler(lean_object* v_method_2255_, lean_object* v_paramType_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_respType_2259_, lean_object* v_inst_2260_, lean_object* v_stateType_2261_, lean_object* v_inst_2262_, lean_object* v_initState_2263_, lean_object* v_handler_2264_, lean_object* v_onDidChange_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler___redArg(v_method_2255_, v_inst_2257_, v_inst_2258_, v_inst_2260_, v_inst_2262_, v_initState_2263_, v_handler_2264_, v_onDidChange_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerCompleteStatefulLspRequestHandler___boxed(lean_object* v_method_2268_, lean_object* v_paramType_2269_, lean_object* v_inst_2270_, lean_object* v_inst_2271_, lean_object* v_respType_2272_, lean_object* v_inst_2273_, lean_object* v_stateType_2274_, lean_object* v_inst_2275_, lean_object* v_initState_2276_, lean_object* v_handler_2277_, lean_object* v_onDidChange_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Server_registerCompleteStatefulLspRequestHandler(v_method_2268_, v_paramType_2269_, v_inst_2270_, v_inst_2271_, v_respType_2272_, v_inst_2273_, v_stateType_2274_, v_inst_2275_, v_initState_2276_, v_handler_2277_, v_onDidChange_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(lean_object* v_method_2281_, lean_object* v_refreshMethod_2282_, lean_object* v_refreshIntervalMs_2283_, lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_initState_2288_, lean_object* v_handler_2289_, lean_object* v_onDidChange_2290_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2292_, 0, v_refreshMethod_2282_);
lean_ctor_set(v___x_2292_, 1, v_refreshIntervalMs_2283_);
v___x_2293_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___redArg(v_method_2281_, v___x_2292_, v_inst_2284_, v_inst_2285_, v_inst_2286_, v_inst_2287_, v_initState_2288_, v_handler_2289_, v_onDidChange_2290_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2294_, lean_object* v_refreshMethod_2295_, lean_object* v_refreshIntervalMs_2296_, lean_object* v_inst_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_inst_2300_, lean_object* v_initState_2301_, lean_object* v_handler_2302_, lean_object* v_onDidChange_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2294_, v_refreshMethod_2295_, v_refreshIntervalMs_2296_, v_inst_2297_, v_inst_2298_, v_inst_2299_, v_inst_2300_, v_initState_2301_, v_handler_2302_, v_onDidChange_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler(lean_object* v_method_2306_, lean_object* v_refreshMethod_2307_, lean_object* v_refreshIntervalMs_2308_, lean_object* v_paramType_2309_, lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_respType_2312_, lean_object* v_inst_2313_, lean_object* v_stateType_2314_, lean_object* v_inst_2315_, lean_object* v_initState_2316_, lean_object* v_handler_2317_, lean_object* v_onDidChange_2318_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___redArg(v_method_2306_, v_refreshMethod_2307_, v_refreshIntervalMs_2308_, v_inst_2310_, v_inst_2311_, v_inst_2313_, v_inst_2315_, v_initState_2316_, v_handler_2317_, v_onDidChange_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___boxed(lean_object* v_method_2321_, lean_object* v_refreshMethod_2322_, lean_object* v_refreshIntervalMs_2323_, lean_object* v_paramType_2324_, lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_respType_2327_, lean_object* v_inst_2328_, lean_object* v_stateType_2329_, lean_object* v_inst_2330_, lean_object* v_initState_2331_, lean_object* v_handler_2332_, lean_object* v_onDidChange_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Server_registerPartialStatefulLspRequestHandler(v_method_2321_, v_refreshMethod_2322_, v_refreshIntervalMs_2323_, v_paramType_2324_, v_inst_2325_, v_inst_2326_, v_respType_2327_, v_inst_2328_, v_stateType_2329_, v_inst_2330_, v_initState_2331_, v_handler_2332_, v_onDidChange_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2336_, lean_object* v_i_2337_, lean_object* v_k_2338_){
_start:
{
lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = lean_array_get_size(v_keys_2336_);
v___x_2340_ = lean_nat_dec_lt(v_i_2337_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_dec(v_i_2337_);
return v___x_2340_;
}
else
{
lean_object* v_k_x27_2341_; uint8_t v___x_2342_; 
v_k_x27_2341_ = lean_array_fget_borrowed(v_keys_2336_, v_i_2337_);
v___x_2342_ = lean_string_dec_eq(v_k_2338_, v_k_x27_2341_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_unsigned_to_nat(1u);
v___x_2344_ = lean_nat_add(v_i_2337_, v___x_2343_);
lean_dec(v_i_2337_);
v_i_2337_ = v___x_2344_;
goto _start;
}
else
{
lean_dec(v_i_2337_);
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2346_, lean_object* v_i_2347_, lean_object* v_k_2348_){
_start:
{
uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_res_2349_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2346_, v_i_2347_, v_k_2348_);
lean_dec_ref(v_k_2348_);
lean_dec_ref(v_keys_2346_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(lean_object* v_x_2351_, size_t v_x_2352_, lean_object* v_x_2353_){
_start:
{
if (lean_obj_tag(v_x_2351_) == 0)
{
lean_object* v_es_2354_; lean_object* v___x_2355_; size_t v___x_2356_; size_t v___x_2357_; lean_object* v_j_2358_; lean_object* v___x_2359_; 
v_es_2354_ = lean_ctor_get(v_x_2351_, 0);
v___x_2355_ = lean_box(2);
v___x_2356_ = ((size_t)31ULL);
v___x_2357_ = lean_usize_land(v_x_2352_, v___x_2356_);
v_j_2358_ = lean_usize_to_nat(v___x_2357_);
v___x_2359_ = lean_array_get_borrowed(v___x_2355_, v_es_2354_, v_j_2358_);
lean_dec(v_j_2358_);
switch(lean_obj_tag(v___x_2359_))
{
case 0:
{
lean_object* v_key_2360_; uint8_t v___x_2361_; 
v_key_2360_ = lean_ctor_get(v___x_2359_, 0);
v___x_2361_ = lean_string_dec_eq(v_x_2353_, v_key_2360_);
return v___x_2361_;
}
case 1:
{
lean_object* v_node_2362_; size_t v___x_2363_; size_t v___x_2364_; 
v_node_2362_ = lean_ctor_get(v___x_2359_, 0);
v___x_2363_ = ((size_t)5ULL);
v___x_2364_ = lean_usize_shift_right(v_x_2352_, v___x_2363_);
v_x_2351_ = v_node_2362_;
v_x_2352_ = v___x_2364_;
goto _start;
}
default: 
{
uint8_t v___x_2366_; 
v___x_2366_ = 0;
return v___x_2366_;
}
}
}
else
{
lean_object* v_ks_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_ks_2367_ = lean_ctor_get(v_x_2351_, 0);
v___x_2368_ = lean_unsigned_to_nat(0u);
v___x_2369_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_ks_2367_, v___x_2368_, v_x_2353_);
return v___x_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg___boxed(lean_object* v_x_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_){
_start:
{
size_t v_x_214__boxed_2373_; uint8_t v_res_2374_; lean_object* v_r_2375_; 
v_x_214__boxed_2373_ = lean_unbox_usize(v_x_2371_);
lean_dec(v_x_2371_);
v_res_2374_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2370_, v_x_214__boxed_2373_, v_x_2372_);
lean_dec_ref(v_x_2372_);
lean_dec_ref(v_x_2370_);
v_r_2375_ = lean_box(v_res_2374_);
return v_r_2375_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
uint64_t v___x_2378_; size_t v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = lean_string_hash(v_x_2377_);
v___x_2379_ = lean_uint64_to_usize(v___x_2378_);
v___x_2380_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2376_, v___x_2379_, v_x_2377_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg___boxed(lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
uint8_t v_res_2383_; lean_object* v_r_2384_; 
v_res_2383_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2381_, v_x_2382_);
lean_dec_ref(v_x_2382_);
lean_dec_ref(v_x_2381_);
v_r_2384_ = lean_box(v_res_2383_);
return v_r_2384_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_isStatefulLspRequestMethod(lean_object* v_method_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = l_Lean_Server_statefulRequestHandlers;
v___x_2388_ = lean_st_ref_get(v___x_2387_);
v___x_2389_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v___x_2388_, v_method_2385_);
lean_dec(v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_isStatefulLspRequestMethod___boxed(lean_object* v_method_2390_, lean_object* v_a_2391_){
_start:
{
uint8_t v_res_2392_; lean_object* v_r_2393_; 
v_res_2392_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_2390_);
lean_dec_ref(v_method_2390_);
v_r_2393_ = lean_box(v_res_2392_);
return v_r_2393_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(lean_object* v_00_u03b2_2394_, lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
uint8_t v___x_2397_; 
v___x_2397_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___redArg(v_x_2395_, v_x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0___boxed(lean_object* v_00_u03b2_2398_, lean_object* v_x_2399_, lean_object* v_x_2400_){
_start:
{
uint8_t v_res_2401_; lean_object* v_r_2402_; 
v_res_2401_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0(v_00_u03b2_2398_, v_x_2399_, v_x_2400_);
lean_dec_ref(v_x_2400_);
lean_dec_ref(v_x_2399_);
v_r_2402_ = lean_box(v_res_2401_);
return v_r_2402_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(lean_object* v_00_u03b2_2403_, lean_object* v_x_2404_, size_t v_x_2405_, lean_object* v_x_2406_){
_start:
{
uint8_t v___x_2407_; 
v___x_2407_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___redArg(v_x_2404_, v_x_2405_, v_x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
size_t v_x_284__boxed_2412_; uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_x_284__boxed_2412_ = lean_unbox_usize(v_x_2410_);
lean_dec(v_x_2410_);
v_res_2413_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0(v_00_u03b2_2408_, v_x_2409_, v_x_284__boxed_2412_, v_x_2411_);
lean_dec_ref(v_x_2411_);
lean_dec_ref(v_x_2409_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2415_, lean_object* v_keys_2416_, lean_object* v_vals_2417_, lean_object* v_heq_2418_, lean_object* v_i_2419_, lean_object* v_k_2420_){
_start:
{
uint8_t v___x_2421_; 
v___x_2421_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___redArg(v_keys_2416_, v_i_2419_, v_k_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2422_, lean_object* v_keys_2423_, lean_object* v_vals_2424_, lean_object* v_heq_2425_, lean_object* v_i_2426_, lean_object* v_k_2427_){
_start:
{
uint8_t v_res_2428_; lean_object* v_r_2429_; 
v_res_2428_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_isStatefulLspRequestMethod_spec__0_spec__0_spec__1(v_00_u03b2_2422_, v_keys_2423_, v_vals_2424_, v_heq_2425_, v_i_2426_, v_k_2427_);
lean_dec_ref(v_k_2427_);
lean_dec_ref(v_vals_2424_);
lean_dec_ref(v_keys_2423_);
v_r_2429_ = lean_box(v_res_2428_);
return v_r_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler(lean_object* v_method_2430_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = l_Lean_Server_statefulRequestHandlers;
v___x_2433_ = lean_st_ref_get(v___x_2432_);
v___x_2434_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_lookupLspRequestHandler_spec__0___redArg(v___x_2433_, v_method_2430_);
lean_dec(v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupStatefulLspRequestHandler___boxed(lean_object* v_method_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2435_);
lean_dec_ref(v_method_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(lean_object* v_as_2438_, size_t v_i_2439_, size_t v_stop_2440_, lean_object* v_b_2441_){
_start:
{
lean_object* v___y_2443_; uint8_t v___x_2447_; 
v___x_2447_ = lean_usize_dec_eq(v_i_2439_, v_stop_2440_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; lean_object* v_snd_2449_; lean_object* v_completeness_2450_; 
v___x_2448_ = lean_array_uget(v_as_2438_, v_i_2439_);
v_snd_2449_ = lean_ctor_get(v___x_2448_, 1);
v_completeness_2450_ = lean_ctor_get(v_snd_2449_, 8);
lean_inc(v_completeness_2450_);
if (lean_obj_tag(v_completeness_2450_) == 1)
{
lean_object* v_fst_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2468_; 
v_fst_2451_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2448_, 1);
lean_dec(v_unused_2469_);
v___x_2453_ = v___x_2448_;
v_isShared_2454_ = v_isSharedCheck_2468_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_fst_2451_);
lean_dec(v___x_2448_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2468_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_refreshMethod_2455_; lean_object* v_refreshIntervalMs_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2467_; 
v_refreshMethod_2455_ = lean_ctor_get(v_completeness_2450_, 0);
v_refreshIntervalMs_2456_ = lean_ctor_get(v_completeness_2450_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_completeness_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2458_ = v_completeness_2450_;
v_isShared_2459_ = v_isSharedCheck_2467_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_refreshIntervalMs_2456_);
lean_inc(v_refreshMethod_2455_);
lean_dec(v_completeness_2450_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2467_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v_refreshIntervalMs_2456_);
lean_ctor_set(v___x_2453_, 0, v_refreshMethod_2455_);
v___x_2461_ = v___x_2453_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_refreshMethod_2455_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_refreshIntervalMs_2456_);
v___x_2461_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2463_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set_tag(v___x_2458_, 0);
lean_ctor_set(v___x_2458_, 1, v___x_2461_);
lean_ctor_set(v___x_2458_, 0, v_fst_2451_);
v___x_2463_ = v___x_2458_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_fst_2451_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_array_push(v_b_2441_, v___x_2463_);
v___y_2443_ = v___x_2464_;
goto v___jp_2442_;
}
}
}
}
}
else
{
lean_dec(v_completeness_2450_);
lean_dec(v___x_2448_);
v___y_2443_ = v_b_2441_;
goto v___jp_2442_;
}
}
else
{
return v_b_2441_;
}
v___jp_2442_:
{
size_t v___x_2444_; size_t v___x_2445_; 
v___x_2444_ = ((size_t)1ULL);
v___x_2445_ = lean_usize_add(v_i_2439_, v___x_2444_);
v_i_2439_ = v___x_2445_;
v_b_2441_ = v___y_2443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2___boxed(lean_object* v_as_2470_, lean_object* v_i_2471_, lean_object* v_stop_2472_, lean_object* v_b_2473_){
_start:
{
size_t v_i_boxed_2474_; size_t v_stop_boxed_2475_; lean_object* v_res_2476_; 
v_i_boxed_2474_ = lean_unbox_usize(v_i_2471_);
lean_dec(v_i_2471_);
v_stop_boxed_2475_ = lean_unbox_usize(v_stop_2472_);
lean_dec(v_stop_2472_);
v_res_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2470_, v_i_boxed_2474_, v_stop_boxed_2475_, v_b_2473_);
lean_dec_ref(v_as_2470_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(lean_object* v_as_2479_, lean_object* v_start_2480_, lean_object* v_stop_2481_){
_start:
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___closed__0));
v___x_2483_ = lean_nat_dec_lt(v_start_2480_, v_stop_2481_);
if (v___x_2483_ == 0)
{
return v___x_2482_;
}
else
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = lean_array_get_size(v_as_2479_);
v___x_2485_ = lean_nat_dec_le(v_stop_2481_, v___x_2484_);
if (v___x_2485_ == 0)
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_nat_dec_lt(v_start_2480_, v___x_2484_);
if (v___x_2486_ == 0)
{
return v___x_2482_;
}
else
{
size_t v___x_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_usize_of_nat(v_start_2480_);
v___x_2488_ = lean_usize_of_nat(v___x_2484_);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2479_, v___x_2487_, v___x_2488_, v___x_2482_);
return v___x_2489_;
}
}
else
{
size_t v___x_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = lean_usize_of_nat(v_start_2480_);
v___x_2491_ = lean_usize_of_nat(v_stop_2481_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1_spec__2(v_as_2479_, v___x_2490_, v___x_2491_, v___x_2482_);
return v___x_2492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1___boxed(lean_object* v_as_2493_, lean_object* v_start_2494_, lean_object* v_stop_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v_as_2493_, v_start_2494_, v_stop_2495_);
lean_dec(v_stop_2495_);
lean_dec(v_start_2494_);
lean_dec_ref(v_as_2493_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_f_2497_, lean_object* v_keys_2498_, lean_object* v_vals_2499_, lean_object* v_i_2500_, lean_object* v_acc_2501_){
_start:
{
lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2502_ = lean_array_get_size(v_keys_2498_);
v___x_2503_ = lean_nat_dec_lt(v_i_2500_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_dec(v_i_2500_);
lean_dec(v_f_2497_);
return v_acc_2501_;
}
else
{
lean_object* v_k_2504_; lean_object* v_v_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_k_2504_ = lean_array_fget_borrowed(v_keys_2498_, v_i_2500_);
v_v_2505_ = lean_array_fget_borrowed(v_vals_2499_, v_i_2500_);
lean_inc(v_f_2497_);
lean_inc(v_v_2505_);
lean_inc(v_k_2504_);
v___x_2506_ = lean_apply_3(v_f_2497_, v_acc_2501_, v_k_2504_, v_v_2505_);
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_nat_add(v_i_2500_, v___x_2507_);
lean_dec(v_i_2500_);
v_i_2500_ = v___x_2508_;
v_acc_2501_ = v___x_2506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_f_2510_, lean_object* v_keys_2511_, lean_object* v_vals_2512_, lean_object* v_i_2513_, lean_object* v_acc_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2510_, v_keys_2511_, v_vals_2512_, v_i_2513_, v_acc_2514_);
lean_dec_ref(v_vals_2512_);
lean_dec_ref(v_keys_2511_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2516_, lean_object* v_x_2517_, lean_object* v_x_2518_){
_start:
{
if (lean_obj_tag(v_x_2517_) == 0)
{
lean_object* v_es_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v_es_2519_ = lean_ctor_get(v_x_2517_, 0);
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_array_get_size(v_es_2519_);
v___x_2522_ = lean_nat_dec_lt(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_dec(v_f_2516_);
return v_x_2518_;
}
else
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_nat_dec_le(v___x_2521_, v___x_2521_);
if (v___x_2523_ == 0)
{
if (v___x_2522_ == 0)
{
lean_dec(v_f_2516_);
return v_x_2518_;
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2521_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2516_, v_es_2519_, v___x_2524_, v___x_2525_, v_x_2518_);
return v___x_2526_;
}
}
else
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = lean_usize_of_nat(v___x_2521_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2516_, v_es_2519_, v___x_2527_, v___x_2528_, v_x_2518_);
return v___x_2529_;
}
}
}
else
{
lean_object* v_ks_2530_; lean_object* v_vs_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_ks_2530_ = lean_ctor_get(v_x_2517_, 0);
v_vs_2531_ = lean_ctor_get(v_x_2517_, 1);
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2516_, v_ks_2530_, v_vs_2531_, v___x_2532_, v_x_2518_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_2534_, lean_object* v_as_2535_, size_t v_i_2536_, size_t v_stop_2537_, lean_object* v_b_2538_){
_start:
{
lean_object* v___y_2540_; uint8_t v___x_2544_; 
v___x_2544_ = lean_usize_dec_eq(v_i_2536_, v_stop_2537_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_array_uget_borrowed(v_as_2535_, v_i_2536_);
switch(lean_obj_tag(v___x_2545_))
{
case 0:
{
lean_object* v_key_2546_; lean_object* v_val_2547_; lean_object* v___x_2548_; 
v_key_2546_ = lean_ctor_get(v___x_2545_, 0);
v_val_2547_ = lean_ctor_get(v___x_2545_, 1);
lean_inc(v_f_2534_);
lean_inc(v_val_2547_);
lean_inc(v_key_2546_);
v___x_2548_ = lean_apply_3(v_f_2534_, v_b_2538_, v_key_2546_, v_val_2547_);
v___y_2540_ = v___x_2548_;
goto v___jp_2539_;
}
case 1:
{
lean_object* v_node_2549_; lean_object* v___x_2550_; 
v_node_2549_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_f_2534_);
v___x_2550_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2534_, v_node_2549_, v_b_2538_);
v___y_2540_ = v___x_2550_;
goto v___jp_2539_;
}
default: 
{
v___y_2540_ = v_b_2538_;
goto v___jp_2539_;
}
}
}
else
{
lean_dec(v_f_2534_);
return v_b_2538_;
}
v___jp_2539_:
{
size_t v___x_2541_; size_t v___x_2542_; 
v___x_2541_ = ((size_t)1ULL);
v___x_2542_ = lean_usize_add(v_i_2536_, v___x_2541_);
v_i_2536_ = v___x_2542_;
v_b_2538_ = v___y_2540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_2551_, lean_object* v_as_2552_, lean_object* v_i_2553_, lean_object* v_stop_2554_, lean_object* v_b_2555_){
_start:
{
size_t v_i_boxed_2556_; size_t v_stop_boxed_2557_; lean_object* v_res_2558_; 
v_i_boxed_2556_ = lean_unbox_usize(v_i_2553_);
lean_dec(v_i_2553_);
v_stop_boxed_2557_ = lean_unbox_usize(v_stop_2554_);
lean_dec(v_stop_2554_);
v_res_2558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2551_, v_as_2552_, v_i_boxed_2556_, v_stop_boxed_2557_, v_b_2555_);
lean_dec_ref(v_as_2552_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2559_, lean_object* v_x_2560_, lean_object* v_x_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2559_, v_x_2560_, v_x_2561_);
lean_dec_ref(v_x_2560_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0(lean_object* v_f_2563_, lean_object* v_x1_2564_, lean_object* v_x2_2565_, lean_object* v_x3_2566_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_apply_3(v_f_2563_, v_x1_2564_, v_x2_2565_, v_x3_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(lean_object* v_map_2568_, lean_object* v_f_2569_, lean_object* v_init_2570_){
_start:
{
lean_object* v___f_2571_; lean_object* v___x_2572_; 
v___f_2571_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2571_, 0, v_f_2569_);
v___x_2572_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v___f_2571_, v_map_2568_, v_init_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg___boxed(lean_object* v_map_2573_, lean_object* v_f_2574_, lean_object* v_init_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_2573_, v_f_2574_, v_init_2575_);
lean_dec_ref(v_map_2573_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___lam__0(lean_object* v_ps_2577_, lean_object* v_k_2578_, lean_object* v_v_2579_){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_k_2578_);
lean_ctor_set(v___x_2580_, 1, v_v_2579_);
v___x_2581_ = lean_array_push(v_ps_2577_, v___x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(lean_object* v_m_2585_){
_start:
{
lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___f_2586_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__0));
v___x_2587_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___closed__1));
v___x_2588_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_m_2585_, v___f_2586_, v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg___boxed(lean_object* v_m_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_2589_);
lean_dec_ref(v_m_2589_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods(){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2592_ = l_Lean_Server_statefulRequestHandlers;
v___x_2593_ = lean_st_ref_get(v___x_2592_);
v___x_2594_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v___x_2593_);
lean_dec(v___x_2593_);
v___x_2595_ = lean_unsigned_to_nat(0u);
v___x_2596_ = lean_array_get_size(v___x_2594_);
v___x_2597_ = l_Array_filterMapM___at___00Lean_Server_partialLspRequestHandlerMethods_spec__1(v___x_2594_, v___x_2595_, v___x_2596_);
lean_dec_ref(v___x_2594_);
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_partialLspRequestHandlerMethods___boxed(lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Server_partialLspRequestHandlerMethods();
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(lean_object* v_00_u03b2_2601_, lean_object* v_m_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___redArg(v_m_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0___boxed(lean_object* v_00_u03b2_2604_, lean_object* v_m_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0(v_00_u03b2_2604_, v_m_2605_);
lean_dec_ref(v_m_2605_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(lean_object* v_00_u03c3_2607_, lean_object* v_00_u03b2_2608_, lean_object* v_map_2609_, lean_object* v_f_2610_, lean_object* v_init_2611_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___redArg(v_map_2609_, v_f_2610_, v_init_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2613_, lean_object* v_00_u03b2_2614_, lean_object* v_map_2615_, lean_object* v_f_2616_, lean_object* v_init_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0(v_00_u03c3_2613_, v_00_u03b2_2614_, v_map_2615_, v_f_2616_, v_init_2617_);
lean_dec_ref(v_map_2615_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(lean_object* v_map_2619_, lean_object* v_f_2620_, lean_object* v_init_2621_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2620_, v_map_2619_, v_init_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_2623_, lean_object* v_f_2624_, lean_object* v_init_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___redArg(v_map_2623_, v_f_2624_, v_init_2625_);
lean_dec_ref(v_map_2623_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2627_, lean_object* v_00_u03b2_2628_, lean_object* v_map_2629_, lean_object* v_f_2630_, lean_object* v_init_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2630_, v_map_2629_, v_init_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2633_, lean_object* v_00_u03b2_2634_, lean_object* v_map_2635_, lean_object* v_f_2636_, lean_object* v_init_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1(v_00_u03c3_2633_, v_00_u03b2_2634_, v_map_2635_, v_f_2636_, v_init_2637_);
lean_dec_ref(v_map_2635_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2639_, lean_object* v_00_u03b1_2640_, lean_object* v_00_u03b2_2641_, lean_object* v_f_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2642_, v_x_2643_, v_x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_2646_, lean_object* v_00_u03b1_2647_, lean_object* v_00_u03b2_2648_, lean_object* v_f_2649_, lean_object* v_x_2650_, lean_object* v_x_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_2646_, v_00_u03b1_2647_, v_00_u03b2_2648_, v_f_2649_, v_x_2650_, v_x_2651_);
lean_dec_ref(v_x_2650_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2653_, lean_object* v_00_u03b2_2654_, lean_object* v_00_u03c3_2655_, lean_object* v_f_2656_, lean_object* v_as_2657_, size_t v_i_2658_, size_t v_stop_2659_, lean_object* v_b_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_2656_, v_as_2657_, v_i_2658_, v_stop_2659_, v_b_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_00_u03b2_2663_, lean_object* v_00_u03c3_2664_, lean_object* v_f_2665_, lean_object* v_as_2666_, lean_object* v_i_2667_, lean_object* v_stop_2668_, lean_object* v_b_2669_){
_start:
{
size_t v_i_boxed_2670_; size_t v_stop_boxed_2671_; lean_object* v_res_2672_; 
v_i_boxed_2670_ = lean_unbox_usize(v_i_2667_);
lean_dec(v_i_2667_);
v_stop_boxed_2671_ = lean_unbox_usize(v_stop_2668_);
lean_dec(v_stop_2668_);
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2662_, v_00_u03b2_2663_, v_00_u03c3_2664_, v_f_2665_, v_as_2666_, v_i_boxed_2670_, v_stop_boxed_2671_, v_b_2669_);
lean_dec_ref(v_as_2666_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_2673_, lean_object* v_00_u03b1_2674_, lean_object* v_00_u03b2_2675_, lean_object* v_f_2676_, lean_object* v_keys_2677_, lean_object* v_vals_2678_, lean_object* v_heq_2679_, lean_object* v_i_2680_, lean_object* v_acc_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_f_2676_, v_keys_2677_, v_vals_2678_, v_i_2680_, v_acc_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_2683_, lean_object* v_00_u03b1_2684_, lean_object* v_00_u03b2_2685_, lean_object* v_f_2686_, lean_object* v_keys_2687_, lean_object* v_vals_2688_, lean_object* v_heq_2689_, lean_object* v_i_2690_, lean_object* v_acc_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00Lean_Server_partialLspRequestHandlerMethods_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03c3_2683_, v_00_u03b1_2684_, v_00_u03b2_2685_, v_f_2686_, v_keys_2687_, v_vals_2688_, v_heq_2689_, v_i_2690_, v_acc_2691_);
lean_dec_ref(v_vals_2688_);
lean_dec_ref(v_keys_2687_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(lean_object* v_inst_2693_, lean_object* v_pureOnDidChange_2694_, lean_object* v_method_2695_, lean_object* v_onDidChange_2696_, lean_object* v_p_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_inc(v_inst_2693_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_inst_2693_);
lean_ctor_set(v___x_2701_, 1, v___y_2698_);
lean_inc_ref(v___y_2699_);
lean_inc_ref(v_p_2697_);
v___x_2702_ = lean_apply_4(v_pureOnDidChange_2694_, v_p_2697_, v___x_2701_, v___y_2699_, lean_box(0));
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v_snd_2704_; lean_object* v___x_2705_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v_snd_2704_ = lean_ctor_get(v_a_2703_, 1);
lean_inc(v_snd_2704_);
lean_dec(v_a_2703_);
v___x_2705_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2695_, v_snd_2704_, v_inst_2693_);
lean_dec(v_inst_2693_);
lean_dec(v_snd_2704_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
lean_inc_ref(v___y_2699_);
v___x_2707_ = lean_apply_4(v_onDidChange_2696_, v_p_2697_, v_a_2706_, v___y_2699_, lean_box(0));
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2725_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2725_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2725_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v_snd_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2723_; 
v_snd_2712_ = lean_ctor_get(v_a_2708_, 1);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_a_2708_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; 
v_unused_2724_ = lean_ctor_get(v_a_2708_, 0);
lean_dec(v_unused_2724_);
v___x_2714_ = v_a_2708_;
v_isShared_2715_ = v_isSharedCheck_2723_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_snd_2712_);
lean_dec(v_a_2708_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2723_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_box(0);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2716_);
v___x_2718_ = v___x_2714_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_snd_2712_);
v___x_2718_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2720_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2718_);
v___x_2720_ = v___x_2710_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
else
{
return v___x_2707_;
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec_ref(v_p_2697_);
lean_dec_ref(v_onDidChange_2696_);
v_a_2726_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2705_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2705_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec_ref(v_p_2697_);
lean_dec_ref(v_onDidChange_2696_);
lean_dec(v_inst_2693_);
v_a_2734_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2702_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2702_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed(lean_object* v_inst_2742_, lean_object* v_pureOnDidChange_2743_, lean_object* v_method_2744_, lean_object* v_onDidChange_2745_, lean_object* v_p_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0(v_inst_2742_, v_pureOnDidChange_2743_, v_method_2744_, v_onDidChange_2745_, v_p_2746_, v___y_2747_, v___y_2748_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v_method_2744_);
return v_res_2750_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__0));
v___x_2753_ = l_Lean_Server_RequestError_internalError(v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__2));
v___x_2756_ = l_Lean_Server_RequestError_internalError(v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(lean_object* v_inst_2757_, lean_object* v_inst_2758_, lean_object* v_pureHandle_2759_, lean_object* v_inst_2760_, lean_object* v_method_2761_, lean_object* v_handler_2762_, lean_object* v_p_2763_, lean_object* v_s_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_inc(v_p_2763_);
v___x_2767_ = lean_apply_1(v_inst_2757_, v_p_2763_);
lean_inc(v_inst_2758_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_inst_2758_);
lean_ctor_set(v___x_2768_, 1, v_s_2764_);
lean_inc_ref(v___y_2765_);
v___x_2769_ = lean_apply_4(v_pureHandle_2759_, v___x_2767_, v___x_2768_, v___y_2765_, lean_box(0));
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2804_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2804_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2804_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v_fst_2774_; lean_object* v_snd_2775_; lean_object* v_response_x3f_2776_; lean_object* v_serialized_2777_; uint8_t v_isComplete_2778_; lean_object* v_a_2780_; 
v_fst_2774_ = lean_ctor_get(v_a_2770_, 0);
lean_inc(v_fst_2774_);
v_snd_2775_ = lean_ctor_get(v_a_2770_, 1);
lean_inc(v_snd_2775_);
lean_dec(v_a_2770_);
v_response_x3f_2776_ = lean_ctor_get(v_fst_2774_, 0);
lean_inc(v_response_x3f_2776_);
v_serialized_2777_ = lean_ctor_get(v_fst_2774_, 1);
lean_inc_ref(v_serialized_2777_);
v_isComplete_2778_ = lean_ctor_get_uint8(v_fst_2774_, sizeof(void*)*2);
lean_dec(v_fst_2774_);
if (lean_obj_tag(v_response_x3f_2776_) == 0)
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_Json_parse(v_serialized_2777_);
if (lean_obj_tag(v___x_2799_) == 1)
{
lean_object* v_a_2800_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v_a_2780_ = v_a_2800_;
goto v___jp_2779_;
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_dec_ref(v___x_2799_);
lean_dec(v_snd_2775_);
lean_del_object(v___x_2772_);
lean_dec(v_p_2763_);
lean_dec_ref(v_handler_2762_);
lean_dec_ref(v_inst_2760_);
lean_dec(v_inst_2758_);
v___x_2801_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__3);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
}
else
{
lean_object* v_val_2803_; 
lean_dec_ref(v_serialized_2777_);
v_val_2803_ = lean_ctor_get(v_response_x3f_2776_, 0);
lean_inc(v_val_2803_);
lean_dec_ref_known(v_response_x3f_2776_, 1);
v_a_2780_ = v_val_2803_;
goto v___jp_2779_;
}
v___jp_2779_:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_apply_1(v_inst_2760_, v_a_2780_);
if (lean_obj_tag(v___x_2781_) == 1)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; 
lean_del_object(v___x_2772_);
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21___redArg(v_method_2761_, v_snd_2775_, v_inst_2758_);
lean_dec(v_inst_2758_);
lean_dec(v_snd_2775_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2785_, 0, v_a_2782_);
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*1, v_isComplete_2778_);
lean_inc_ref(v___y_2765_);
v___x_2786_ = lean_apply_5(v_handler_2762_, v_p_2763_, v___x_2785_, v_a_2784_, v___y_2765_, lean_box(0));
return v___x_2786_;
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_a_2782_);
lean_dec(v_p_2763_);
lean_dec_ref(v_handler_2762_);
v_a_2787_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2783_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2783_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2797_; 
lean_dec_ref(v___x_2781_);
lean_dec(v_snd_2775_);
lean_dec(v_p_2763_);
lean_dec_ref(v_handler_2762_);
lean_dec(v_inst_2758_);
v___x_2795_ = lean_obj_once(&l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1, &l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1_once, _init_l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___closed__1);
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 1);
lean_ctor_set(v___x_2772_, 0, v___x_2795_);
v___x_2797_ = v___x_2772_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v_p_2763_);
lean_dec_ref(v_handler_2762_);
lean_dec_ref(v_inst_2760_);
lean_dec(v_inst_2758_);
v_a_2805_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2769_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2769_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed(lean_object* v_inst_2813_, lean_object* v_inst_2814_, lean_object* v_pureHandle_2815_, lean_object* v_inst_2816_, lean_object* v_method_2817_, lean_object* v_handler_2818_, lean_object* v_p_2819_, lean_object* v_s_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1(v_inst_2813_, v_inst_2814_, v_pureHandle_2815_, v_inst_2816_, v_method_2817_, v_handler_2818_, v_p_2819_, v_s_2820_, v___y_2821_);
lean_dec_ref(v___y_2821_);
lean_dec_ref(v_method_2817_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg(lean_object* v_method_2825_, lean_object* v_inst_2826_, lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_handler_2832_, lean_object* v_onDidChange_2833_){
_start:
{
uint8_t v___x_2835_; 
v___x_2835_ = l_Lean_initializing();
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_dec_ref(v_onDidChange_2833_);
lean_dec_ref(v_handler_2832_);
lean_dec(v_inst_2831_);
lean_dec_ref(v_inst_2830_);
lean_dec_ref(v_inst_2829_);
lean_dec_ref(v_inst_2828_);
lean_dec_ref(v_inst_2827_);
lean_dec_ref(v_inst_2826_);
v___x_2836_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_2837_ = lean_string_append(v___x_2836_, v_method_2825_);
lean_dec_ref(v_method_2825_);
v___x_2838_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___redArg___closed__1));
v___x_2839_ = lean_string_append(v___x_2837_, v___x_2838_);
v___x_2840_ = lean_mk_io_user_error(v___x_2839_);
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_2825_);
if (lean_obj_tag(v___x_2842_) == 1)
{
lean_object* v_val_2843_; lean_object* v_pureHandle_2844_; lean_object* v_pureOnDidChange_2845_; lean_object* v_initState_2846_; lean_object* v_completeness_2847_; lean_object* v___x_2848_; 
v_val_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_val_2843_);
lean_dec_ref_known(v___x_2842_, 1);
v_pureHandle_2844_ = lean_ctor_get(v_val_2843_, 1);
lean_inc_ref(v_pureHandle_2844_);
v_pureOnDidChange_2845_ = lean_ctor_get(v_val_2843_, 3);
lean_inc_ref(v_pureOnDidChange_2845_);
v_initState_2846_ = lean_ctor_get(v_val_2843_, 6);
lean_inc(v_initState_2846_);
v_completeness_2847_ = lean_ctor_get(v_val_2843_, 8);
lean_inc(v_completeness_2847_);
lean_dec(v_val_2843_);
v___x_2848_ = l___private_Lean_Server_Requests_0__Lean_Server_getIOState_x21___redArg(v_method_2825_, v_initState_2846_, v_inst_2831_);
lean_dec(v_initState_2846_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___f_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
lean_inc_ref_n(v_method_2825_, 2);
lean_inc_n(v_inst_2831_, 2);
v___f_2850_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2850_, 0, v_inst_2831_);
lean_closure_set(v___f_2850_, 1, v_pureOnDidChange_2845_);
lean_closure_set(v___f_2850_, 2, v_method_2825_);
lean_closure_set(v___f_2850_, 3, v_onDidChange_2833_);
v___f_2851_ = lean_alloc_closure((void*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___lam__1___boxed), 10, 6);
lean_closure_set(v___f_2851_, 0, v_inst_2827_);
lean_closure_set(v___f_2851_, 1, v_inst_2831_);
lean_closure_set(v___f_2851_, 2, v_pureHandle_2844_);
lean_closure_set(v___f_2851_, 3, v_inst_2829_);
lean_closure_set(v___f_2851_, 4, v_method_2825_);
lean_closure_set(v___f_2851_, 5, v_handler_2832_);
v___x_2852_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___redArg(v_method_2825_, v_completeness_2847_, v_inst_2826_, v_inst_2828_, v_inst_2830_, v_inst_2831_, v_a_2849_, v___f_2851_, v___f_2850_);
return v___x_2852_;
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_completeness_2847_);
lean_dec_ref(v_pureOnDidChange_2845_);
lean_dec_ref(v_pureHandle_2844_);
lean_dec_ref(v_onDidChange_2833_);
lean_dec_ref(v_handler_2832_);
lean_dec(v_inst_2831_);
lean_dec_ref(v_inst_2830_);
lean_dec_ref(v_inst_2829_);
lean_dec_ref(v_inst_2828_);
lean_dec_ref(v_inst_2827_);
lean_dec_ref(v_inst_2826_);
lean_dec_ref(v_method_2825_);
v_a_2853_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2848_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2848_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
lean_dec(v___x_2842_);
lean_dec_ref(v_onDidChange_2833_);
lean_dec_ref(v_handler_2832_);
lean_dec(v_inst_2831_);
lean_dec_ref(v_inst_2830_);
lean_dec_ref(v_inst_2829_);
lean_dec_ref(v_inst_2828_);
lean_dec_ref(v_inst_2827_);
lean_dec_ref(v_inst_2826_);
v___x_2861_ = ((lean_object*)(l_Lean_Server_chainStatefulLspRequestHandler___redArg___closed__0));
v___x_2862_ = lean_string_append(v___x_2861_, v_method_2825_);
lean_dec_ref(v_method_2825_);
v___x_2863_ = ((lean_object*)(l_Lean_Server_chainLspRequestHandler___redArg___closed__1));
v___x_2864_ = lean_string_append(v___x_2862_, v___x_2863_);
v___x_2865_ = lean_mk_io_user_error(v___x_2864_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___redArg___boxed(lean_object* v_method_2867_, lean_object* v_inst_2868_, lean_object* v_inst_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_handler_2874_, lean_object* v_onDidChange_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2867_, v_inst_2868_, v_inst_2869_, v_inst_2870_, v_inst_2871_, v_inst_2872_, v_inst_2873_, v_handler_2874_, v_onDidChange_2875_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler(lean_object* v_method_2878_, lean_object* v_paramType_2879_, lean_object* v_inst_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_respType_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_stateType_2886_, lean_object* v_inst_2887_, lean_object* v_handler_2888_, lean_object* v_onDidChange_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_Server_chainStatefulLspRequestHandler___redArg(v_method_2878_, v_inst_2880_, v_inst_2881_, v_inst_2882_, v_inst_2884_, v_inst_2885_, v_inst_2887_, v_handler_2888_, v_onDidChange_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainStatefulLspRequestHandler___boxed(lean_object* v_method_2892_, lean_object* v_paramType_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_respType_2897_, lean_object* v_inst_2898_, lean_object* v_inst_2899_, lean_object* v_stateType_2900_, lean_object* v_inst_2901_, lean_object* v_handler_2902_, lean_object* v_onDidChange_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Server_chainStatefulLspRequestHandler(v_method_2892_, v_paramType_2893_, v_inst_2894_, v_inst_2895_, v_inst_2896_, v_respType_2897_, v_inst_2898_, v_inst_2899_, v_stateType_2900_, v_inst_2901_, v_handler_2902_, v_onDidChange_2903_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0(lean_object* v_p_2906_, lean_object* v_x_2907_, lean_object* v_handler_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_onDidChange_2911_; lean_object* v___x_2912_; 
v_onDidChange_2911_ = lean_ctor_get(v_handler_2908_, 4);
lean_inc_ref(v_onDidChange_2911_);
lean_dec_ref(v_handler_2908_);
lean_inc_ref(v___y_2909_);
v___x_2912_ = lean_apply_3(v_onDidChange_2911_, v_p_2906_, v___y_2909_, lean_box(0));
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___lam__0___boxed(lean_object* v_p_2913_, lean_object* v_x_2914_, lean_object* v_handler_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Server_handleOnDidChange___lam__0(v_p_2913_, v_x_2914_, v_handler_2915_, v___y_2916_);
lean_dec_ref(v___y_2916_);
lean_dec_ref(v_x_2914_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(lean_object* v_f_2919_, lean_object* v_x_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
lean_inc_ref(v___y_2923_);
v___x_2925_ = lean_apply_4(v_f_2919_, v___y_2921_, v___y_2922_, v___y_2923_, lean_box(0));
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed(lean_object* v_f_2926_, lean_object* v_x_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0(v_f_2926_, v_x_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec_ref(v___y_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2933_, lean_object* v_keys_2934_, lean_object* v_vals_2935_, lean_object* v_i_2936_, lean_object* v_acc_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_keys_2934_);
v___x_2941_ = lean_nat_dec_lt(v_i_2936_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec(v_i_2936_);
lean_dec_ref(v_f_2933_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_acc_2937_);
return v___x_2942_;
}
else
{
lean_object* v_k_2943_; lean_object* v_v_2944_; lean_object* v___x_2945_; 
v_k_2943_ = lean_array_fget_borrowed(v_keys_2934_, v_i_2936_);
v_v_2944_ = lean_array_fget_borrowed(v_vals_2935_, v_i_2936_);
lean_inc_ref(v_f_2933_);
lean_inc_ref(v___y_2938_);
lean_inc(v_v_2944_);
lean_inc(v_k_2943_);
v___x_2945_ = lean_apply_5(v_f_2933_, v_acc_2937_, v_k_2943_, v_v_2944_, v___y_2938_, lean_box(0));
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = lean_unsigned_to_nat(1u);
v___x_2948_ = lean_nat_add(v_i_2936_, v___x_2947_);
lean_dec(v_i_2936_);
v_i_2936_ = v___x_2948_;
v_acc_2937_ = v_a_2946_;
goto _start;
}
else
{
lean_dec(v_i_2936_);
lean_dec_ref(v_f_2933_);
return v___x_2945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2950_, lean_object* v_keys_2951_, lean_object* v_vals_2952_, lean_object* v_i_2953_, lean_object* v_acc_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2950_, v_keys_2951_, v_vals_2952_, v_i_2953_, v_acc_2954_, v___y_2955_);
lean_dec_ref(v___y_2955_);
lean_dec_ref(v_vals_2952_);
lean_dec_ref(v_keys_2951_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2958_, lean_object* v_x_2959_, lean_object* v_x_2960_, lean_object* v___y_2961_){
_start:
{
if (lean_obj_tag(v_x_2959_) == 0)
{
lean_object* v_es_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2983_; 
v_es_2963_ = lean_ctor_get(v_x_2959_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_x_2959_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2965_ = v_x_2959_;
v_isShared_2966_ = v_isSharedCheck_2983_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_es_2963_);
lean_dec(v_x_2959_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2983_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2967_ = lean_unsigned_to_nat(0u);
v___x_2968_ = lean_array_get_size(v_es_2963_);
v___x_2969_ = lean_nat_dec_lt(v___x_2967_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2971_; 
lean_dec_ref(v_es_2963_);
lean_dec_ref(v_f_2958_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v_x_2960_);
v___x_2971_ = v___x_2965_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_x_2960_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
else
{
uint8_t v___x_2973_; 
v___x_2973_ = lean_nat_dec_le(v___x_2968_, v___x_2968_);
if (v___x_2973_ == 0)
{
if (v___x_2969_ == 0)
{
lean_object* v___x_2975_; 
lean_dec_ref(v_es_2963_);
lean_dec_ref(v_f_2958_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v_x_2960_);
v___x_2975_ = v___x_2965_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_x_2960_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
else
{
size_t v___x_2977_; size_t v___x_2978_; lean_object* v___x_2979_; 
lean_del_object(v___x_2965_);
v___x_2977_ = ((size_t)0ULL);
v___x_2978_ = lean_usize_of_nat(v___x_2968_);
v___x_2979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2958_, v_es_2963_, v___x_2977_, v___x_2978_, v_x_2960_, v___y_2961_);
lean_dec_ref(v_es_2963_);
return v___x_2979_;
}
}
else
{
size_t v___x_2980_; size_t v___x_2981_; lean_object* v___x_2982_; 
lean_del_object(v___x_2965_);
v___x_2980_ = ((size_t)0ULL);
v___x_2981_ = lean_usize_of_nat(v___x_2968_);
v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2958_, v_es_2963_, v___x_2980_, v___x_2981_, v_x_2960_, v___y_2961_);
lean_dec_ref(v_es_2963_);
return v___x_2982_;
}
}
}
}
else
{
lean_object* v_ks_2984_; lean_object* v_vs_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_ks_2984_ = lean_ctor_get(v_x_2959_, 0);
lean_inc_ref(v_ks_2984_);
v_vs_2985_ = lean_ctor_get(v_x_2959_, 1);
lean_inc_ref(v_vs_2985_);
lean_dec_ref_known(v_x_2959_, 2);
v___x_2986_ = lean_unsigned_to_nat(0u);
v___x_2987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2958_, v_ks_2984_, v_vs_2985_, v___x_2986_, v_x_2960_, v___y_2961_);
lean_dec_ref(v_vs_2985_);
lean_dec_ref(v_ks_2984_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2988_, lean_object* v_as_2989_, size_t v_i_2990_, size_t v_stop_2991_, lean_object* v_b_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_a_2996_; lean_object* v___y_3001_; uint8_t v___x_3003_; 
v___x_3003_ = lean_usize_dec_eq(v_i_2990_, v_stop_2991_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_array_uget_borrowed(v_as_2989_, v_i_2990_);
switch(lean_obj_tag(v___x_3004_))
{
case 0:
{
lean_object* v_key_3005_; lean_object* v_val_3006_; lean_object* v___x_3007_; 
v_key_3005_ = lean_ctor_get(v___x_3004_, 0);
v_val_3006_ = lean_ctor_get(v___x_3004_, 1);
lean_inc_ref(v_f_2988_);
lean_inc_ref(v___y_2993_);
lean_inc(v_val_3006_);
lean_inc(v_key_3005_);
v___x_3007_ = lean_apply_5(v_f_2988_, v_b_2992_, v_key_3005_, v_val_3006_, v___y_2993_, lean_box(0));
v___y_3001_ = v___x_3007_;
goto v___jp_3000_;
}
case 1:
{
lean_object* v_node_3008_; lean_object* v___x_3009_; 
v_node_3008_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_node_3008_);
lean_inc_ref(v_f_2988_);
v___x_3009_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_2988_, v_node_3008_, v_b_2992_, v___y_2993_);
v___y_3001_ = v___x_3009_;
goto v___jp_3000_;
}
default: 
{
v_a_2996_ = v_b_2992_;
goto v___jp_2995_;
}
}
}
else
{
lean_object* v___x_3010_; 
lean_dec_ref(v_f_2988_);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_b_2992_);
return v___x_3010_;
}
v___jp_2995_:
{
size_t v___x_2997_; size_t v___x_2998_; 
v___x_2997_ = ((size_t)1ULL);
v___x_2998_ = lean_usize_add(v_i_2990_, v___x_2997_);
v_i_2990_ = v___x_2998_;
v_b_2992_ = v_a_2996_;
goto _start;
}
v___jp_3000_:
{
if (lean_obj_tag(v___y_3001_) == 0)
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___y_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___y_3001_, 1);
v_a_2996_ = v_a_3002_;
goto v___jp_2995_;
}
else
{
lean_dec_ref(v_f_2988_);
return v___y_3001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3011_, lean_object* v_as_3012_, lean_object* v_i_3013_, lean_object* v_stop_3014_, lean_object* v_b_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
size_t v_i_boxed_3018_; size_t v_stop_boxed_3019_; lean_object* v_res_3020_; 
v_i_boxed_3018_ = lean_unbox_usize(v_i_3013_);
lean_dec(v_i_3013_);
v_stop_boxed_3019_ = lean_unbox_usize(v_stop_3014_);
lean_dec(v_stop_3014_);
v_res_3020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3011_, v_as_3012_, v_i_boxed_3018_, v_stop_boxed_3019_, v_b_3015_, v___y_3016_);
lean_dec_ref(v___y_3016_);
lean_dec_ref(v_as_3012_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3021_, lean_object* v_x_3022_, lean_object* v_x_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3021_, v_x_3022_, v_x_3023_, v___y_3024_);
lean_dec_ref(v___y_3024_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(lean_object* v_map_3027_, lean_object* v_f_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___f_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___f_3031_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3031_, 0, v_f_3028_);
v___x_3032_ = lean_box(0);
v___x_3033_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v___f_3031_, v_map_3027_, v___x_3032_, v___y_3029_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg___boxed(lean_object* v_map_3034_, lean_object* v_f_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3034_, v_f_3035_, v___y_3036_);
lean_dec_ref(v___y_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange(lean_object* v_p_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___f_3044_; lean_object* v___x_3045_; 
v___x_3042_ = l_Lean_Server_statefulRequestHandlers;
v___x_3043_ = lean_st_ref_get(v___x_3042_);
v___f_3044_ = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3044_, 0, v_p_3039_);
v___x_3045_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v___x_3043_, v___f_3044_, v_a_3040_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleOnDidChange___boxed(lean_object* v_p_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Server_handleOnDidChange(v_p_3046_, v_a_3047_);
lean_dec_ref(v_a_3047_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(lean_object* v_00_u03b2_3050_, lean_object* v_map_3051_, lean_object* v_f_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___redArg(v_map_3051_, v_f_3052_, v___y_3053_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0___boxed(lean_object* v_00_u03b2_3056_, lean_object* v_map_3057_, lean_object* v_f_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0(v_00_u03b2_3056_, v_map_3057_, v_f_3058_, v___y_3059_);
lean_dec_ref(v___y_3059_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(lean_object* v_map_3062_, lean_object* v_f_3063_, lean_object* v_init_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3063_, v_map_3062_, v_init_3064_, v___y_3065_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg___boxed(lean_object* v_map_3068_, lean_object* v_f_3069_, lean_object* v_init_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___redArg(v_map_3068_, v_f_3069_, v_init_3070_, v___y_3071_);
lean_dec_ref(v___y_3071_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(lean_object* v_00_u03c3_3074_, lean_object* v_00_u03b2_3075_, lean_object* v_map_3076_, lean_object* v_f_3077_, lean_object* v_init_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3077_, v_map_3076_, v_init_3078_, v___y_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3082_, lean_object* v_00_u03b2_3083_, lean_object* v_map_3084_, lean_object* v_f_3085_, lean_object* v_init_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0(v_00_u03c3_3082_, v_00_u03b2_3083_, v_map_3084_, v_f_3085_, v_init_3086_, v___y_3087_);
lean_dec_ref(v___y_3087_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3090_, lean_object* v_00_u03b1_3091_, lean_object* v_00_u03b2_3092_, lean_object* v_f_3093_, lean_object* v_x_3094_, lean_object* v_x_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___redArg(v_f_3093_, v_x_3094_, v_x_3095_, v___y_3096_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3099_, lean_object* v_00_u03b1_3100_, lean_object* v_00_u03b2_3101_, lean_object* v_f_3102_, lean_object* v_x_3103_, lean_object* v_x_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1(v_00_u03c3_3099_, v_00_u03b1_3100_, v_00_u03b2_3101_, v_f_3102_, v_x_3103_, v_x_3104_, v___y_3105_);
lean_dec_ref(v___y_3105_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3108_, lean_object* v_00_u03b2_3109_, lean_object* v_00_u03c3_3110_, lean_object* v_f_3111_, lean_object* v_as_3112_, size_t v_i_3113_, size_t v_stop_3114_, lean_object* v_b_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3111_, v_as_3112_, v_i_3113_, v_stop_3114_, v_b_3115_, v___y_3116_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3119_, lean_object* v_00_u03b2_3120_, lean_object* v_00_u03c3_3121_, lean_object* v_f_3122_, lean_object* v_as_3123_, lean_object* v_i_3124_, lean_object* v_stop_3125_, lean_object* v_b_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
size_t v_i_boxed_3129_; size_t v_stop_boxed_3130_; lean_object* v_res_3131_; 
v_i_boxed_3129_ = lean_unbox_usize(v_i_3124_);
lean_dec(v_i_3124_);
v_stop_boxed_3130_ = lean_unbox_usize(v_stop_3125_);
lean_dec(v_stop_3125_);
v_res_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3119_, v_00_u03b2_3120_, v_00_u03c3_3121_, v_f_3122_, v_as_3123_, v_i_boxed_3129_, v_stop_boxed_3130_, v_b_3126_, v___y_3127_);
lean_dec_ref(v___y_3127_);
lean_dec_ref(v_as_3123_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3132_, lean_object* v_00_u03b1_3133_, lean_object* v_00_u03b2_3134_, lean_object* v_f_3135_, lean_object* v_keys_3136_, lean_object* v_vals_3137_, lean_object* v_heq_3138_, lean_object* v_i_3139_, lean_object* v_acc_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3135_, v_keys_3136_, v_vals_3137_, v_i_3139_, v_acc_3140_, v___y_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3144_, lean_object* v_00_u03b1_3145_, lean_object* v_00_u03b2_3146_, lean_object* v_f_3147_, lean_object* v_keys_3148_, lean_object* v_vals_3149_, lean_object* v_heq_3150_, lean_object* v_i_3151_, lean_object* v_acc_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_Server_handleOnDidChange_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3144_, v_00_u03b1_3145_, v_00_u03b2_3146_, v_f_3147_, v_keys_3148_, v_vals_3149_, v_heq_3150_, v_i_3151_, v_acc_3152_, v___y_3153_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v_vals_3149_);
lean_dec_ref(v_keys_3148_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* v_method_3158_, lean_object* v_params_3159_, lean_object* v_a_3160_){
_start:
{
uint8_t v___x_3162_; 
v___x_3162_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3158_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3179_; 
v___x_3163_ = l_Lean_Server_lookupLspRequestHandler(v_method_3158_);
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3179_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3179_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
if (lean_obj_tag(v_a_3164_) == 0)
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3174_; 
lean_dec(v_params_3159_);
v___x_3168_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3169_ = lean_string_append(v___x_3168_, v_method_3158_);
v___x_3170_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3171_ = lean_string_append(v___x_3169_, v___x_3170_);
v___x_3172_ = l_Lean_Server_RequestError_internalError(v___x_3171_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set_tag(v___x_3166_, 1);
lean_ctor_set(v___x_3166_, 0, v___x_3172_);
v___x_3174_ = v___x_3166_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
else
{
lean_object* v_val_3176_; lean_object* v_handle_3177_; lean_object* v___x_3178_; 
lean_del_object(v___x_3166_);
v_val_3176_ = lean_ctor_get(v_a_3164_, 0);
lean_inc(v_val_3176_);
lean_dec_ref_known(v_a_3164_, 1);
v_handle_3177_ = lean_ctor_get(v_val_3176_, 1);
lean_inc_ref(v_handle_3177_);
lean_dec(v_val_3176_);
lean_inc_ref(v_a_3160_);
v___x_3178_ = lean_apply_3(v_handle_3177_, v_params_3159_, v_a_3160_, lean_box(0));
return v___x_3178_;
}
}
}
else
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3158_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v_params_3159_);
v___x_3181_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__0));
v___x_3182_ = lean_string_append(v___x_3181_, v_method_3158_);
v___x_3183_ = ((lean_object*)(l_Lean_Server_handleLspRequest___closed__1));
v___x_3184_ = lean_string_append(v___x_3182_, v___x_3183_);
v___x_3185_ = l_Lean_Server_RequestError_internalError(v___x_3184_);
v___x_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
return v___x_3186_;
}
else
{
lean_object* v_val_3187_; lean_object* v_handle_3188_; lean_object* v___x_3189_; 
v_val_3187_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v___x_3180_, 1);
v_handle_3188_ = lean_ctor_get(v_val_3187_, 2);
lean_inc_ref(v_handle_3188_);
lean_dec(v_val_3187_);
lean_inc_ref(v_a_3160_);
v___x_3189_ = lean_apply_3(v_handle_3188_, v_params_3159_, v_a_3160_, lean_box(0));
return v___x_3189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest___boxed(lean_object* v_method_3190_, lean_object* v_params_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_Server_handleLspRequest(v_method_3190_, v_params_3191_, v_a_3192_);
lean_dec_ref(v_a_3192_);
lean_dec_ref(v_method_3190_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* v_method_3195_, lean_object* v_params_3196_){
_start:
{
uint8_t v___x_3198_; 
v___x_3198_ = l_Lean_Server_isStatefulLspRequestMethod(v_method_3195_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3215_; 
v___x_3199_ = l_Lean_Server_lookupLspRequestHandler(v_method_3195_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3215_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3215_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
if (lean_obj_tag(v_a_3200_) == 0)
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
lean_dec(v_params_3196_);
v___x_3204_ = l_Lean_Server_RequestError_methodNotFound(v_method_3195_);
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3205_);
v___x_3207_ = v___x_3202_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
else
{
lean_object* v_val_3209_; lean_object* v_fileSource_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v_val_3209_ = lean_ctor_get(v_a_3200_, 0);
lean_inc(v_val_3209_);
lean_dec_ref_known(v_a_3200_, 1);
v_fileSource_3210_ = lean_ctor_get(v_val_3209_, 0);
lean_inc_ref(v_fileSource_3210_);
lean_dec(v_val_3209_);
v___x_3211_ = lean_apply_1(v_fileSource_3210_, v_params_3196_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3211_);
v___x_3213_ = v___x_3202_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_Server_lookupStatefulLspRequestHandler(v_method_3195_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec(v_params_3196_);
v___x_3217_ = l_Lean_Server_RequestError_methodNotFound(v_method_3195_);
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
else
{
lean_object* v_val_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3229_; 
v_val_3220_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3222_ = v___x_3216_;
v_isShared_3223_ = v_isSharedCheck_3229_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_val_3220_);
lean_dec(v___x_3216_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3229_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_fileSource_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
v_fileSource_3224_ = lean_ctor_get(v_val_3220_, 0);
lean_inc_ref(v_fileSource_3224_);
lean_dec(v_val_3220_);
v___x_3225_ = lean_apply_1(v_fileSource_3224_, v_params_3196_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3225_);
v___x_3227_ = v___x_3222_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest___boxed(lean_object* v_method_3230_, lean_object* v_params_3231_, lean_object* v_a_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Lean_Server_routeLspRequest(v_method_3230_, v_params_3231_);
lean_dec_ref(v_method_3230_);
return v_res_3233_;
}
}
lean_object* runtime_initialize_Lean_Server_RequestCancellation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileSource(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker_Utils(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_RequestCancellation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_3846811639____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_requestHandlers = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_requestHandlers);
lean_dec_ref(res);
res = l___private_Lean_Server_Requests_0__Lean_Server_initFn_00___x40_Lean_Server_Requests_2517033524____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_statefulRequestHandlers = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_statefulRequestHandlers);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Requests(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_RequestCancellation(uint8_t builtin);
lean_object* initialize_Lean_Server_FileSource(uint8_t builtin);
lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Requests(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_RequestCancellation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Requests(builtin);
}
#ifdef __cplusplus
}
#endif

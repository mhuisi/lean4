// Lean compiler output
// Module: Lean.Server.FileWorker.SemanticHighlighting
// Imports: public import Lean.Server.Requests import Lean.DocString.View
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
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Doc_InlineView_of(lean_object*);
lean_object* l_Lean_Doc_ArgView_of(lean_object*);
lean_object* l_Lean_Doc_ArgValView_of(lean_object*);
lean_object* l_Lean_Doc_BlockView_of(lean_object*);
lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoCodeBlockLine(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
extern lean_object* l_Lean_Parser_Term_identProjKind;
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_SemanticTokenType_toNat(uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_AsyncList_waitUntil___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_string_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object*);
lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object*, uint32_t, lean_object*);
lean_object* l_Lean_FileMap_lspRangeOfStx_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqSemanticTokenType_beq(uint8_t, uint8_t);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(lean_object*);
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonSemanticTokens_toJson(lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Server_statefulRequestHandlers;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokenType_fromJson(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Lsp_instToJsonSemanticTokenType_toJson(uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
uint64_t l_Lean_Lsp_instHashablePosition_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_Lsp_instHashableSemanticTokenType_hash(uint8_t);
lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__3_value;
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(138, 85, 70, 0, 206, 11, 146, 59)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__5_value;
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(64, 200, 114, 122, 5, 59, 103, 167)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prop"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__7_value;
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__7_value),LEAN_SCALAR_PTR_LITERAL(200, 217, 246, 140, 179, 171, 30, 243)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__8 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__9 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__9_value;
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__9_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__10 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__10_value;
static const lean_array_object l_Lean_Server_FileWorker_noHighlightKinds___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__10_value)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__11 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_noHighlightKinds = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__11_value;
static const lean_string_object l_Lean_Server_FileWorker_docKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_docKinds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "plainDocComment"};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__1_value;
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(130, 89, 58, 24, 132, 56, 253, 137)}};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_docKinds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__3_value;
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value;
static const lean_string_object l_Lean_Server_FileWorker_docKinds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "moduleDoc"};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__5_value;
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(249, 71, 187, 113, 90, 175, 60, 199)}};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value;
static const lean_array_object l_Lean_Server_FileWorker_docKinds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value)}};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_docKinds = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__7_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0;
static const lean_string_object l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "admit"};
static const lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1_value;
static lean_once_cell_t l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2;
static const lean_string_object l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3_value;
static lean_once_cell_t l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4;
static const lean_string_object l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "#exit"};
static const lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5_value;
static lean_once_cell_t l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken = (const lean_object*)&l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken = (const lean_object*)&l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FileWorker"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "AbsoluteLspSemanticToken"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 14, 27, 113, 182, 128, 119, 36)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 244, 165, 17, 43, 66, 230, 94)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 67, 188, 228, 198, 126, 180, 88)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "tailPos"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(90, 23, 179, 28, 157, 202, 35, 235)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(112, 109, 54, 158, 248, 169, 165, 159)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22_value),LEAN_SCALAR_PTR_LITERAL(119, 157, 28, 87, 58, 42, 19, 197)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken = (const lean_object*)&l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goVal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goOrderedItem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "document"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__4 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(234, 113, 152, 229, 184, 253, 250, 127)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goOrderedItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pipeProj"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__2_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__2_value),LEAN_SCALAR_PTR_LITERAL(104, 78, 204, 170, 128, 130, 207, 24)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__4_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__4_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5_value;
static const lean_array_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6_value;
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__7_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\t"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_dbgShowTokens___closed__0;
static lean_once_cell_t l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_dbgShowTokens___closed__1;
static const lean_closure_object l_Lean_Server_FileWorker_dbgShowTokens___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_dbgShowTokens___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_dbgShowTokens___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_dbgShowTokens___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Server_FileWorker_dbgShowTokens___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_dbgShowTokens___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "SemanticTokensState"};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value;
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 14, 27, 113, 182, 128, 119, 36)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value),LEAN_SCALAR_PTR_LITERAL(114, 29, 136, 15, 114, 206, 151, 105)}};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instTypeNameSemanticTokensState = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instInhabitedSemanticTokensState;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot parse request params: "};
static const lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "textDocument/semanticTokens/range"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "textDocument/semanticTokens/full"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "workspace/semanticTokens/refresh"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(lean_object* v_k_64_, lean_object* v_v_65_, lean_object* v_t_66_){
_start:
{
if (lean_obj_tag(v_t_66_) == 0)
{
lean_object* v_size_67_; lean_object* v_k_68_; lean_object* v_v_69_; lean_object* v_l_70_; lean_object* v_r_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_351_; 
v_size_67_ = lean_ctor_get(v_t_66_, 0);
v_k_68_ = lean_ctor_get(v_t_66_, 1);
v_v_69_ = lean_ctor_get(v_t_66_, 2);
v_l_70_ = lean_ctor_get(v_t_66_, 3);
v_r_71_ = lean_ctor_get(v_t_66_, 4);
v_isSharedCheck_351_ = !lean_is_exclusive(v_t_66_);
if (v_isSharedCheck_351_ == 0)
{
v___x_73_ = v_t_66_;
v_isShared_74_ = v_isSharedCheck_351_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_r_71_);
lean_inc(v_l_70_);
lean_inc(v_v_69_);
lean_inc(v_k_68_);
lean_inc(v_size_67_);
lean_dec(v_t_66_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_351_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint8_t v___x_75_; 
v___x_75_ = lean_string_compare(v_k_64_, v_k_68_);
switch(v___x_75_)
{
case 0:
{
lean_object* v_impl_76_; lean_object* v___x_77_; 
lean_dec(v_size_67_);
v_impl_76_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_64_, v_v_65_, v_l_70_);
v___x_77_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_71_) == 0)
{
lean_object* v_size_78_; lean_object* v_size_79_; lean_object* v_k_80_; lean_object* v_v_81_; lean_object* v_l_82_; lean_object* v_r_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_size_78_ = lean_ctor_get(v_r_71_, 0);
v_size_79_ = lean_ctor_get(v_impl_76_, 0);
lean_inc(v_size_79_);
v_k_80_ = lean_ctor_get(v_impl_76_, 1);
lean_inc(v_k_80_);
v_v_81_ = lean_ctor_get(v_impl_76_, 2);
lean_inc(v_v_81_);
v_l_82_ = lean_ctor_get(v_impl_76_, 3);
lean_inc(v_l_82_);
v_r_83_ = lean_ctor_get(v_impl_76_, 4);
lean_inc(v_r_83_);
v___x_84_ = lean_unsigned_to_nat(3u);
v___x_85_ = lean_nat_mul(v___x_84_, v_size_78_);
v___x_86_ = lean_nat_dec_lt(v___x_85_, v_size_79_);
lean_dec(v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
lean_dec(v_r_83_);
lean_dec(v_l_82_);
lean_dec(v_v_81_);
lean_dec(v_k_80_);
v___x_87_ = lean_nat_add(v___x_77_, v_size_79_);
lean_dec(v_size_79_);
v___x_88_ = lean_nat_add(v___x_87_, v_size_78_);
lean_dec(v___x_87_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 3, v_impl_76_);
lean_ctor_set(v___x_73_, 0, v___x_88_);
v___x_90_ = v___x_73_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_91_, 3, v_impl_76_);
lean_ctor_set(v_reuseFailAlloc_91_, 4, v_r_71_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
else
{
lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_157_; 
v_isSharedCheck_157_ = !lean_is_exclusive(v_impl_76_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; lean_object* v_unused_161_; lean_object* v_unused_162_; 
v_unused_158_ = lean_ctor_get(v_impl_76_, 4);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_impl_76_, 3);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_impl_76_, 2);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_impl_76_, 1);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_impl_76_, 0);
lean_dec(v_unused_162_);
v___x_93_ = v_impl_76_;
v_isShared_94_ = v_isSharedCheck_157_;
goto v_resetjp_92_;
}
else
{
lean_dec(v_impl_76_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_157_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_size_95_; lean_object* v_size_96_; lean_object* v_k_97_; lean_object* v_v_98_; lean_object* v_l_99_; lean_object* v_r_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_size_95_ = lean_ctor_get(v_l_82_, 0);
v_size_96_ = lean_ctor_get(v_r_83_, 0);
v_k_97_ = lean_ctor_get(v_r_83_, 1);
v_v_98_ = lean_ctor_get(v_r_83_, 2);
v_l_99_ = lean_ctor_get(v_r_83_, 3);
v_r_100_ = lean_ctor_get(v_r_83_, 4);
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_nat_mul(v___x_101_, v_size_95_);
v___x_103_ = lean_nat_dec_lt(v_size_96_, v___x_102_);
lean_dec(v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_132_; 
lean_inc(v_r_100_);
lean_inc(v_l_99_);
lean_inc(v_v_98_);
lean_inc(v_k_97_);
v_isSharedCheck_132_ = !lean_is_exclusive(v_r_83_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; lean_object* v_unused_134_; lean_object* v_unused_135_; lean_object* v_unused_136_; lean_object* v_unused_137_; 
v_unused_133_ = lean_ctor_get(v_r_83_, 4);
lean_dec(v_unused_133_);
v_unused_134_ = lean_ctor_get(v_r_83_, 3);
lean_dec(v_unused_134_);
v_unused_135_ = lean_ctor_get(v_r_83_, 2);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_r_83_, 1);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_r_83_, 0);
lean_dec(v_unused_137_);
v___x_105_ = v_r_83_;
v_isShared_106_ = v_isSharedCheck_132_;
goto v_resetjp_104_;
}
else
{
lean_dec(v_r_83_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_132_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___x_120_; lean_object* v___y_122_; 
v___x_107_ = lean_nat_add(v___x_77_, v_size_79_);
lean_dec(v_size_79_);
v___x_108_ = lean_nat_add(v___x_107_, v_size_78_);
lean_dec(v___x_107_);
v___x_120_ = lean_nat_add(v___x_77_, v_size_95_);
if (lean_obj_tag(v_l_99_) == 0)
{
lean_object* v_size_130_; 
v_size_130_ = lean_ctor_get(v_l_99_, 0);
lean_inc(v_size_130_);
v___y_122_ = v_size_130_;
goto v___jp_121_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___y_122_ = v___x_131_;
goto v___jp_121_;
}
v___jp_109_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_nat_add(v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec(v___y_111_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 4, v_r_71_);
lean_ctor_set(v___x_105_, 3, v_r_100_);
lean_ctor_set(v___x_105_, 2, v_v_69_);
lean_ctor_set(v___x_105_, 1, v_k_68_);
lean_ctor_set(v___x_105_, 0, v___x_113_);
v___x_115_ = v___x_105_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v_r_100_);
lean_ctor_set(v_reuseFailAlloc_119_, 4, v_r_71_);
v___x_115_ = v_reuseFailAlloc_119_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_117_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___x_115_);
lean_ctor_set(v___x_93_, 3, v___y_110_);
lean_ctor_set(v___x_93_, 2, v_v_98_);
lean_ctor_set(v___x_93_, 1, v_k_97_);
lean_ctor_set(v___x_93_, 0, v___x_108_);
v___x_117_ = v___x_93_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_k_97_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_v_98_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v___y_110_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_nat_add(v___x_120_, v___y_122_);
lean_dec(v___y_122_);
lean_dec(v___x_120_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_l_99_);
lean_ctor_set(v___x_73_, 3, v_l_82_);
lean_ctor_set(v___x_73_, 2, v_v_81_);
lean_ctor_set(v___x_73_, 1, v_k_80_);
lean_ctor_set(v___x_73_, 0, v___x_123_);
v___x_125_ = v___x_73_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_k_80_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_v_81_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_l_82_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v_l_99_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; 
v___x_126_ = lean_nat_add(v___x_77_, v_size_78_);
if (lean_obj_tag(v_r_100_) == 0)
{
lean_object* v_size_127_; 
v_size_127_ = lean_ctor_get(v_r_100_, 0);
lean_inc(v_size_127_);
v___y_110_ = v___x_125_;
v___y_111_ = v___x_126_;
v___y_112_ = v_size_127_;
goto v___jp_109_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___y_110_ = v___x_125_;
v___y_111_ = v___x_126_;
v___y_112_ = v___x_128_;
goto v___jp_109_;
}
}
}
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
lean_del_object(v___x_73_);
v___x_138_ = lean_nat_add(v___x_77_, v_size_79_);
lean_dec(v_size_79_);
v___x_139_ = lean_nat_add(v___x_138_, v_size_78_);
lean_dec(v___x_138_);
v___x_140_ = lean_nat_add(v___x_77_, v_size_78_);
v___x_141_ = lean_nat_add(v___x_140_, v_size_96_);
lean_dec(v___x_140_);
lean_inc_ref(v_r_71_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v_r_71_);
lean_ctor_set(v___x_93_, 3, v_r_83_);
lean_ctor_set(v___x_93_, 2, v_v_69_);
lean_ctor_set(v___x_93_, 1, v_k_68_);
lean_ctor_set(v___x_93_, 0, v___x_141_);
v___x_143_ = v___x_93_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_r_83_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v_r_71_);
v___x_143_ = v_reuseFailAlloc_156_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_isSharedCheck_150_ = !lean_is_exclusive(v_r_71_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; lean_object* v_unused_155_; 
v_unused_151_ = lean_ctor_get(v_r_71_, 4);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_r_71_, 3);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_r_71_, 2);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_r_71_, 1);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_r_71_, 0);
lean_dec(v_unused_155_);
v___x_145_ = v_r_71_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_r_71_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v___x_143_);
lean_ctor_set(v___x_145_, 3, v_l_82_);
lean_ctor_set(v___x_145_, 2, v_v_81_);
lean_ctor_set(v___x_145_, 1, v_k_80_);
lean_ctor_set(v___x_145_, 0, v___x_139_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_k_80_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_v_81_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v_l_82_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v___x_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_163_; 
v_l_163_ = lean_ctor_get(v_impl_76_, 3);
lean_inc(v_l_163_);
if (lean_obj_tag(v_l_163_) == 0)
{
lean_object* v_r_164_; lean_object* v_k_165_; lean_object* v_v_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_177_; 
v_r_164_ = lean_ctor_get(v_impl_76_, 4);
v_k_165_ = lean_ctor_get(v_impl_76_, 1);
v_v_166_ = lean_ctor_get(v_impl_76_, 2);
v_isSharedCheck_177_ = !lean_is_exclusive(v_impl_76_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; lean_object* v_unused_179_; 
v_unused_178_ = lean_ctor_get(v_impl_76_, 3);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_impl_76_, 0);
lean_dec(v_unused_179_);
v___x_168_ = v_impl_76_;
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_r_164_);
lean_inc(v_v_166_);
lean_inc(v_k_165_);
lean_dec(v_impl_76_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_164_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 3, v_r_164_);
lean_ctor_set(v___x_168_, 2, v_v_69_);
lean_ctor_set(v___x_168_, 1, v_k_68_);
lean_ctor_set(v___x_168_, 0, v___x_77_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_r_164_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_r_164_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_172_);
lean_ctor_set(v___x_73_, 3, v_l_163_);
lean_ctor_set(v___x_73_, 2, v_v_166_);
lean_ctor_set(v___x_73_, 1, v_k_165_);
lean_ctor_set(v___x_73_, 0, v___x_170_);
v___x_174_ = v___x_73_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_165_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_166_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_l_163_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_r_180_; 
v_r_180_ = lean_ctor_get(v_impl_76_, 4);
lean_inc(v_r_180_);
if (lean_obj_tag(v_r_180_) == 0)
{
lean_object* v_k_181_; lean_object* v_v_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_205_; 
v_k_181_ = lean_ctor_get(v_impl_76_, 1);
v_v_182_ = lean_ctor_get(v_impl_76_, 2);
v_isSharedCheck_205_ = !lean_is_exclusive(v_impl_76_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; 
v_unused_206_ = lean_ctor_get(v_impl_76_, 4);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_impl_76_, 3);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_impl_76_, 0);
lean_dec(v_unused_208_);
v___x_184_ = v_impl_76_;
v_isShared_185_ = v_isSharedCheck_205_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_v_182_);
lean_inc(v_k_181_);
lean_dec(v_impl_76_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_205_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_k_186_; lean_object* v_v_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_201_; 
v_k_186_ = lean_ctor_get(v_r_180_, 1);
v_v_187_ = lean_ctor_get(v_r_180_, 2);
v_isSharedCheck_201_ = !lean_is_exclusive(v_r_180_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_202_ = lean_ctor_get(v_r_180_, 4);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_r_180_, 3);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_r_180_, 0);
lean_dec(v_unused_204_);
v___x_189_ = v_r_180_;
v_isShared_190_ = v_isSharedCheck_201_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_v_187_);
lean_inc(v_k_186_);
lean_dec(v_r_180_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_201_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(3u);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 4, v_l_163_);
lean_ctor_set(v___x_189_, 3, v_l_163_);
lean_ctor_set(v___x_189_, 2, v_v_182_);
lean_ctor_set(v___x_189_, 1, v_k_181_);
lean_ctor_set(v___x_189_, 0, v___x_77_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_k_181_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_v_182_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_l_163_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_l_163_);
v___x_193_ = v_reuseFailAlloc_200_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 4, v_l_163_);
lean_ctor_set(v___x_184_, 2, v_v_69_);
lean_ctor_set(v___x_184_, 1, v_k_68_);
lean_ctor_set(v___x_184_, 0, v___x_77_);
v___x_195_ = v___x_184_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_l_163_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_l_163_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_195_);
lean_ctor_set(v___x_73_, 3, v___x_193_);
lean_ctor_set(v___x_73_, 2, v_v_187_);
lean_ctor_set(v___x_73_, 1, v_k_186_);
lean_ctor_set(v___x_73_, 0, v___x_191_);
v___x_197_ = v___x_73_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_unsigned_to_nat(2u);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_r_180_);
lean_ctor_set(v___x_73_, 3, v_impl_76_);
lean_ctor_set(v___x_73_, 0, v___x_209_);
v___x_211_ = v___x_73_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_impl_76_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_r_180_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
case 1:
{
lean_object* v___x_214_; 
lean_dec(v_v_69_);
lean_dec(v_k_68_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 2, v_v_65_);
lean_ctor_set(v___x_73_, 1, v_k_64_);
v___x_214_ = v___x_73_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_size_67_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_64_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_65_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_r_71_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
default: 
{
lean_object* v_impl_216_; lean_object* v___x_217_; 
lean_dec(v_size_67_);
v_impl_216_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_64_, v_v_65_, v_r_71_);
v___x_217_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_70_) == 0)
{
lean_object* v_size_218_; lean_object* v_size_219_; lean_object* v_k_220_; lean_object* v_v_221_; lean_object* v_l_222_; lean_object* v_r_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_size_218_ = lean_ctor_get(v_l_70_, 0);
v_size_219_ = lean_ctor_get(v_impl_216_, 0);
lean_inc(v_size_219_);
v_k_220_ = lean_ctor_get(v_impl_216_, 1);
lean_inc(v_k_220_);
v_v_221_ = lean_ctor_get(v_impl_216_, 2);
lean_inc(v_v_221_);
v_l_222_ = lean_ctor_get(v_impl_216_, 3);
lean_inc(v_l_222_);
v_r_223_ = lean_ctor_get(v_impl_216_, 4);
lean_inc(v_r_223_);
v___x_224_ = lean_unsigned_to_nat(3u);
v___x_225_ = lean_nat_mul(v___x_224_, v_size_218_);
v___x_226_ = lean_nat_dec_lt(v___x_225_, v_size_219_);
lean_dec(v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
lean_dec(v_r_223_);
lean_dec(v_l_222_);
lean_dec(v_v_221_);
lean_dec(v_k_220_);
v___x_227_ = lean_nat_add(v___x_217_, v_size_218_);
v___x_228_ = lean_nat_add(v___x_227_, v_size_219_);
lean_dec(v_size_219_);
lean_dec(v___x_227_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_impl_216_);
lean_ctor_set(v___x_73_, 0, v___x_228_);
v___x_230_ = v___x_73_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_impl_216_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
else
{
lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v_impl_216_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_296_ = lean_ctor_get(v_impl_216_, 4);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_impl_216_, 3);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_impl_216_, 2);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_impl_216_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_impl_216_, 0);
lean_dec(v_unused_300_);
v___x_233_ = v_impl_216_;
v_isShared_234_ = v_isSharedCheck_295_;
goto v_resetjp_232_;
}
else
{
lean_dec(v_impl_216_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_295_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_size_235_; lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_l_238_; lean_object* v_r_239_; lean_object* v_size_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_size_235_ = lean_ctor_get(v_l_222_, 0);
v_k_236_ = lean_ctor_get(v_l_222_, 1);
v_v_237_ = lean_ctor_get(v_l_222_, 2);
v_l_238_ = lean_ctor_get(v_l_222_, 3);
v_r_239_ = lean_ctor_get(v_l_222_, 4);
v_size_240_ = lean_ctor_get(v_r_223_, 0);
v___x_241_ = lean_unsigned_to_nat(2u);
v___x_242_ = lean_nat_mul(v___x_241_, v_size_240_);
v___x_243_ = lean_nat_dec_lt(v_size_235_, v___x_242_);
lean_dec(v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_271_; 
lean_inc(v_r_239_);
lean_inc(v_l_238_);
lean_inc(v_v_237_);
lean_inc(v_k_236_);
v_isSharedCheck_271_ = !lean_is_exclusive(v_l_222_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_272_ = lean_ctor_get(v_l_222_, 4);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_l_222_, 3);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_l_222_, 2);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_l_222_, 1);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_l_222_, 0);
lean_dec(v_unused_276_);
v___x_245_ = v_l_222_;
v_isShared_246_ = v_isSharedCheck_271_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_l_222_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_271_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_261_; 
v___x_247_ = lean_nat_add(v___x_217_, v_size_218_);
v___x_248_ = lean_nat_add(v___x_247_, v_size_219_);
lean_dec(v_size_219_);
if (lean_obj_tag(v_l_238_) == 0)
{
lean_object* v_size_269_; 
v_size_269_ = lean_ctor_get(v_l_238_, 0);
lean_inc(v_size_269_);
v___y_261_ = v_size_269_;
goto v___jp_260_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___y_261_ = v___x_270_;
goto v___jp_260_;
}
v___jp_249_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_nat_add(v___y_250_, v___y_252_);
lean_dec(v___y_252_);
lean_dec(v___y_250_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 4, v_r_223_);
lean_ctor_set(v___x_245_, 3, v_r_239_);
lean_ctor_set(v___x_245_, 2, v_v_221_);
lean_ctor_set(v___x_245_, 1, v_k_220_);
lean_ctor_set(v___x_245_, 0, v___x_253_);
v___x_255_ = v___x_245_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_220_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_221_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_r_239_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_r_223_);
v___x_255_ = v_reuseFailAlloc_259_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 4, v___x_255_);
lean_ctor_set(v___x_233_, 3, v___y_251_);
lean_ctor_set(v___x_233_, 2, v_v_237_);
lean_ctor_set(v___x_233_, 1, v_k_236_);
lean_ctor_set(v___x_233_, 0, v___x_248_);
v___x_257_ = v___x_233_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_236_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_237_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v___y_251_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_nat_add(v___x_247_, v___y_261_);
lean_dec(v___y_261_);
lean_dec(v___x_247_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_l_238_);
lean_ctor_set(v___x_73_, 0, v___x_262_);
v___x_264_ = v___x_73_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_l_238_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; 
v___x_265_ = lean_nat_add(v___x_217_, v_size_240_);
if (lean_obj_tag(v_r_239_) == 0)
{
lean_object* v_size_266_; 
v_size_266_ = lean_ctor_get(v_r_239_, 0);
lean_inc(v_size_266_);
v___y_250_ = v___x_265_;
v___y_251_ = v___x_264_;
v___y_252_ = v_size_266_;
goto v___jp_249_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___y_250_ = v___x_265_;
v___y_251_ = v___x_264_;
v___y_252_ = v___x_267_;
goto v___jp_249_;
}
}
}
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
lean_del_object(v___x_73_);
v___x_277_ = lean_nat_add(v___x_217_, v_size_218_);
v___x_278_ = lean_nat_add(v___x_277_, v_size_219_);
lean_dec(v_size_219_);
v___x_279_ = lean_nat_add(v___x_277_, v_size_235_);
lean_dec(v___x_277_);
lean_inc_ref(v_l_70_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 4, v_l_222_);
lean_ctor_set(v___x_233_, 3, v_l_70_);
lean_ctor_set(v___x_233_, 2, v_v_69_);
lean_ctor_set(v___x_233_, 1, v_k_68_);
lean_ctor_set(v___x_233_, 0, v___x_279_);
v___x_281_ = v___x_233_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v_l_222_);
v___x_281_ = v_reuseFailAlloc_294_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_isSharedCheck_288_ = !lean_is_exclusive(v_l_70_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_289_ = lean_ctor_get(v_l_70_, 4);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_l_70_, 3);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_l_70_, 2);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_l_70_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_l_70_, 0);
lean_dec(v_unused_293_);
v___x_283_ = v_l_70_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_dec(v_l_70_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 4, v_r_223_);
lean_ctor_set(v___x_283_, 3, v___x_281_);
lean_ctor_set(v___x_283_, 2, v_v_221_);
lean_ctor_set(v___x_283_, 1, v_k_220_);
lean_ctor_set(v___x_283_, 0, v___x_278_);
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_220_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_221_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_r_223_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_301_; 
v_l_301_ = lean_ctor_get(v_impl_216_, 3);
lean_inc(v_l_301_);
if (lean_obj_tag(v_l_301_) == 0)
{
lean_object* v_r_302_; lean_object* v_k_303_; lean_object* v_v_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_327_; 
v_r_302_ = lean_ctor_get(v_impl_216_, 4);
v_k_303_ = lean_ctor_get(v_impl_216_, 1);
v_v_304_ = lean_ctor_get(v_impl_216_, 2);
v_isSharedCheck_327_ = !lean_is_exclusive(v_impl_216_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; 
v_unused_328_ = lean_ctor_get(v_impl_216_, 3);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_impl_216_, 0);
lean_dec(v_unused_329_);
v___x_306_ = v_impl_216_;
v_isShared_307_ = v_isSharedCheck_327_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_r_302_);
lean_inc(v_v_304_);
lean_inc(v_k_303_);
lean_dec(v_impl_216_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_327_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_323_; 
v_k_308_ = lean_ctor_get(v_l_301_, 1);
v_v_309_ = lean_ctor_get(v_l_301_, 2);
v_isSharedCheck_323_ = !lean_is_exclusive(v_l_301_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; 
v_unused_324_ = lean_ctor_get(v_l_301_, 4);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_l_301_, 3);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_l_301_, 0);
lean_dec(v_unused_326_);
v___x_311_ = v_l_301_;
v_isShared_312_ = v_isSharedCheck_323_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_v_309_);
lean_inc(v_k_308_);
lean_dec(v_l_301_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_323_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_302_, 2);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 4, v_r_302_);
lean_ctor_set(v___x_311_, 3, v_r_302_);
lean_ctor_set(v___x_311_, 2, v_v_69_);
lean_ctor_set(v___x_311_, 1, v_k_68_);
lean_ctor_set(v___x_311_, 0, v___x_217_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v_r_302_);
lean_ctor_set(v_reuseFailAlloc_322_, 4, v_r_302_);
v___x_315_ = v_reuseFailAlloc_322_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_317_; 
lean_inc(v_r_302_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 3, v_r_302_);
lean_ctor_set(v___x_306_, 0, v___x_217_);
v___x_317_ = v___x_306_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_k_303_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_v_304_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_r_302_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_r_302_);
v___x_317_ = v_reuseFailAlloc_321_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_317_);
lean_ctor_set(v___x_73_, 3, v___x_315_);
lean_ctor_set(v___x_73_, 2, v_v_309_);
lean_ctor_set(v___x_73_, 1, v_k_308_);
lean_ctor_set(v___x_73_, 0, v___x_313_);
v___x_319_ = v___x_73_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
else
{
lean_object* v_r_330_; 
v_r_330_ = lean_ctor_get(v_impl_216_, 4);
lean_inc(v_r_330_);
if (lean_obj_tag(v_r_330_) == 0)
{
lean_object* v_k_331_; lean_object* v_v_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_343_; 
v_k_331_ = lean_ctor_get(v_impl_216_, 1);
v_v_332_ = lean_ctor_get(v_impl_216_, 2);
v_isSharedCheck_343_ = !lean_is_exclusive(v_impl_216_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; lean_object* v_unused_345_; lean_object* v_unused_346_; 
v_unused_344_ = lean_ctor_get(v_impl_216_, 4);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_impl_216_, 3);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_impl_216_, 0);
lean_dec(v_unused_346_);
v___x_334_ = v_impl_216_;
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_v_332_);
lean_inc(v_k_331_);
lean_dec(v_impl_216_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(3u);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 4, v_l_301_);
lean_ctor_set(v___x_334_, 2, v_v_69_);
lean_ctor_set(v___x_334_, 1, v_k_68_);
lean_ctor_set(v___x_334_, 0, v___x_217_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_l_301_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_l_301_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_r_330_);
lean_ctor_set(v___x_73_, 3, v___x_338_);
lean_ctor_set(v___x_73_, 2, v_v_332_);
lean_ctor_set(v___x_73_, 1, v_k_331_);
lean_ctor_set(v___x_73_, 0, v___x_336_);
v___x_340_ = v___x_73_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_331_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_332_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_r_330_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = lean_unsigned_to_nat(2u);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_impl_216_);
lean_ctor_set(v___x_73_, 3, v_r_330_);
lean_ctor_set(v___x_73_, 0, v___x_347_);
v___x_349_ = v___x_73_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_r_330_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_impl_216_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
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
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_k_64_);
lean_ctor_set(v___x_353_, 2, v_v_65_);
lean_ctor_set(v___x_353_, 3, v_t_66_);
lean_ctor_set(v___x_353_, 4, v_t_66_);
return v___x_353_;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0(void){
_start:
{
lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_354_ = lean_box(1);
v___x_355_ = 23;
v___x_356_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__3));
v___x_357_ = lean_box(v___x_355_);
v___x_358_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_356_, v___x_357_, v___x_354_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2(void){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_360_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0);
v___x_361_ = 23;
v___x_362_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1));
v___x_363_ = lean_box(v___x_361_);
v___x_364_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_362_, v___x_363_, v___x_360_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4(void){
_start:
{
lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2);
v___x_367_ = 23;
v___x_368_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3));
v___x_369_ = lean_box(v___x_367_);
v___x_370_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_368_, v___x_369_, v___x_366_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6(void){
_start:
{
lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4);
v___x_373_ = 23;
v___x_374_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5));
v___x_375_ = lean_box(v___x_373_);
v___x_376_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_374_, v___x_375_, v___x_372_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0(lean_object* v_00_u03b2_378_, lean_object* v_k_379_, lean_object* v_v_380_, lean_object* v_t_381_, lean_object* v_hl_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_379_, v_v_380_, v_t_381_);
return v___x_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
lean_object* v_pos_386_; lean_object* v_tailPos_387_; uint8_t v_type_388_; lean_object* v_priority_389_; lean_object* v_pos_390_; lean_object* v_tailPos_391_; uint8_t v_type_392_; lean_object* v_priority_393_; uint8_t v___x_394_; 
v_pos_386_ = lean_ctor_get(v_x_384_, 0);
v_tailPos_387_ = lean_ctor_get(v_x_384_, 1);
v_type_388_ = lean_ctor_get_uint8(v_x_384_, sizeof(void*)*3);
v_priority_389_ = lean_ctor_get(v_x_384_, 2);
v_pos_390_ = lean_ctor_get(v_x_385_, 0);
v_tailPos_391_ = lean_ctor_get(v_x_385_, 1);
v_type_392_ = lean_ctor_get_uint8(v_x_385_, sizeof(void*)*3);
v_priority_393_ = lean_ctor_get(v_x_385_, 2);
v___x_394_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_386_, v_pos_390_);
if (v___x_394_ == 0)
{
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = l_Lean_Lsp_instBEqPosition_beq(v_tailPos_387_, v_tailPos_391_);
if (v___x_395_ == 0)
{
return v___x_395_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_Lsp_instBEqSemanticTokenType_beq(v_type_388_, v_type_392_);
if (v___x_396_ == 0)
{
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_eq(v_priority_389_, v_priority_393_);
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq___boxed(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(v_x_398_, v_x_399_);
lean_dec_ref(v_x_399_);
lean_dec_ref(v_x_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT uint64_t l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(lean_object* v_x_404_){
_start:
{
lean_object* v_pos_405_; lean_object* v_tailPos_406_; uint8_t v_type_407_; lean_object* v_priority_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; 
v_pos_405_ = lean_ctor_get(v_x_404_, 0);
v_tailPos_406_ = lean_ctor_get(v_x_404_, 1);
v_type_407_ = lean_ctor_get_uint8(v_x_404_, sizeof(void*)*3);
v_priority_408_ = lean_ctor_get(v_x_404_, 2);
v___x_409_ = 0ULL;
v___x_410_ = l_Lean_Lsp_instHashablePosition_hash(v_pos_405_);
v___x_411_ = lean_uint64_mix_hash(v___x_409_, v___x_410_);
v___x_412_ = l_Lean_Lsp_instHashablePosition_hash(v_tailPos_406_);
v___x_413_ = lean_uint64_mix_hash(v___x_411_, v___x_412_);
v___x_414_ = l_Lean_Lsp_instHashableSemanticTokenType_hash(v_type_407_);
v___x_415_ = lean_uint64_mix_hash(v___x_413_, v___x_414_);
v___x_416_ = lean_uint64_of_nat(v_priority_408_);
v___x_417_ = lean_uint64_mix_hash(v___x_415_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash___boxed(lean_object* v_x_418_){
_start:
{
uint64_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(v_x_418_);
lean_dec_ref(v_x_418_);
v_r_420_ = lean_box_uint64(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(lean_object* v_j_423_, lean_object* v_k_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = l_Lean_Json_getObjValD(v_j_423_, v_k_424_);
v___x_426_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0___boxed(lean_object* v_j_427_, lean_object* v_k_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_j_427_, v_k_428_);
lean_dec_ref(v_k_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(lean_object* v_j_430_, lean_object* v_k_431_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = l_Lean_Json_getObjValD(v_j_430_, v_k_431_);
v___x_433_ = l_Lean_Lsp_instFromJsonSemanticTokenType_fromJson(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1___boxed(lean_object* v_j_434_, lean_object* v_k_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_j_434_, v_k_435_);
lean_dec_ref(v_k_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(lean_object* v_j_437_, lean_object* v_k_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = l_Lean_Json_getObjValD(v_j_437_, v_k_438_);
v___x_440_ = l_Lean_Json_getNat_x3f(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2___boxed(lean_object* v_j_441_, lean_object* v_k_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_j_441_, v_k_442_);
lean_dec_ref(v_k_442_);
return v_res_443_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5(void){
_start:
{
uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = 1;
v___x_454_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4));
v___x_455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_454_, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6));
v___x_458_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5);
v___x_459_ = lean_string_append(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9(void){
_start:
{
uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = 1;
v___x_463_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8));
v___x_464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_463_, v___x_462_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9);
v___x_466_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_467_ = lean_string_append(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_470_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10);
v___x_471_ = lean_string_append(v___x_470_, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15(void){
_start:
{
uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = 1;
v___x_476_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14));
v___x_477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15);
v___x_479_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_480_ = lean_string_append(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_482_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16);
v___x_483_ = lean_string_append(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19(void){
_start:
{
uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = 1;
v___x_487_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18));
v___x_488_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_487_, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19);
v___x_490_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_491_ = lean_string_append(v___x_490_, v___x_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_493_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20);
v___x_494_ = lean_string_append(v___x_493_, v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24(void){
_start:
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = 1;
v___x_499_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23));
v___x_500_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24);
v___x_502_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_503_ = lean_string_append(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_505_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25);
v___x_506_ = lean_string_append(v___x_505_, v___x_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson(lean_object* v_json_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
lean_inc(v_json_507_);
v___x_509_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_507_, v___x_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_json_507_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_519_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_519_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_519_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12);
v___x_515_ = lean_string_append(v___x_514_, v_a_510_);
lean_dec(v_a_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
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
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_json_507_);
v_a_520_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_509_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_509_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 0);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_a_528_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_509_, 1);
v___x_529_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
lean_inc(v_json_507_);
v___x_530_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_507_, v___x_529_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_528_);
lean_dec(v_json_507_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_540_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17);
v___x_536_ = lean_string_append(v___x_535_, v_a_531_);
lean_dec(v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_536_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_528_);
lean_dec(v_json_507_);
v_a_541_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_530_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_530_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_a_549_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_530_, 1);
v___x_550_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
lean_inc(v_json_507_);
v___x_551_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_json_507_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_549_);
lean_dec(v_a_528_);
lean_dec(v_json_507_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_561_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21);
v___x_557_ = lean_string_append(v___x_556_, v_a_552_);
lean_dec(v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_a_549_);
lean_dec(v_a_528_);
lean_dec(v_json_507_);
v_a_562_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_551_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_551_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 0);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_a_570_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_551_, 1);
v___x_571_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_572_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_json_507_, v___x_571_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_a_570_);
lean_dec(v_a_549_);
lean_dec(v_a_528_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_582_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26);
v___x_578_ = lean_string_append(v___x_577_, v_a_573_);
lean_dec(v_a_573_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_a_570_);
lean_dec(v_a_549_);
lean_dec(v_a_528_);
v_a_583_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_572_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_572_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 0);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_600_; 
v_a_591_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_600_ == 0)
{
v___x_593_ = v___x_572_;
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_572_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_598_; 
v___x_595_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_595_, 0, v_a_528_);
lean_ctor_set(v___x_595_, 1, v_a_549_);
lean_ctor_set(v___x_595_, 2, v_a_591_);
v___x_596_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*3, v___x_596_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_595_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
if (lean_obj_tag(v_a_603_) == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_array_to_list(v_a_604_);
return v___x_605_;
}
else
{
lean_object* v_head_606_; lean_object* v_tail_607_; lean_object* v___x_608_; 
v_head_606_ = lean_ctor_get(v_a_603_, 0);
lean_inc(v_head_606_);
v_tail_607_ = lean_ctor_get(v_a_603_, 1);
lean_inc(v_tail_607_);
lean_dec_ref_known(v_a_603_, 2);
v___x_608_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_604_, v_head_606_);
v_a_603_ = v_tail_607_;
v_a_604_ = v___x_608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson(lean_object* v_x_612_){
_start:
{
lean_object* v_pos_613_; lean_object* v_tailPos_614_; uint8_t v_type_615_; lean_object* v_priority_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_pos_613_ = lean_ctor_get(v_x_612_, 0);
lean_inc_ref(v_pos_613_);
v_tailPos_614_ = lean_ctor_get(v_x_612_, 1);
lean_inc_ref(v_tailPos_614_);
v_type_615_ = lean_ctor_get_uint8(v_x_612_, sizeof(void*)*3);
v_priority_616_ = lean_ctor_get(v_x_612_, 2);
lean_inc(v_priority_616_);
lean_dec_ref(v_x_612_);
v___x_617_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
v___x_618_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_613_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
v___x_623_ = l_Lean_Lsp_instToJsonPosition_toJson(v_tailPos_614_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_620_);
v___x_626_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
v___x_627_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_615_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_620_);
v___x_630_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_631_ = l_Lean_JsonNumber_fromNat(v_priority_616_);
v___x_632_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_630_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_620_);
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_620_);
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_629_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_625_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_621_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = ((lean_object*)(l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0));
v___x_640_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(v___x_638_, v___x_639_);
v___x_641_ = l_Lean_Json_mkObj(v___x_640_);
lean_dec(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(lean_object* v_text_644_, lean_object* v_beginPos_645_, lean_object* v_endPos_x3f_646_, lean_object* v_as_647_, size_t v_i_648_, size_t v_stop_649_, lean_object* v_b_650_){
_start:
{
lean_object* v___y_652_; uint8_t v___x_656_; 
v___x_656_ = lean_usize_dec_eq(v_i_648_, v_stop_649_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v_stx_658_; uint8_t v_type_659_; lean_object* v_priority_660_; lean_object* v___x_661_; 
v___x_657_ = lean_array_uget_borrowed(v_as_647_, v_i_648_);
v_stx_658_ = lean_ctor_get(v___x_657_, 0);
v_type_659_ = lean_ctor_get_uint8(v___x_657_, sizeof(void*)*2);
v_priority_660_ = lean_ctor_get(v___x_657_, 1);
v___x_661_ = l_Lean_Syntax_getPos_x3f(v_stx_658_, v___x_656_);
if (lean_obj_tag(v___x_661_) == 0)
{
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_663_; 
v_val_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = l_Lean_Syntax_getTailPos_x3f(v_stx_658_, v___x_656_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec(v_val_662_);
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
lean_object* v_val_664_; uint8_t v___y_666_; uint8_t v___x_671_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_671_ = lean_nat_dec_le(v_beginPos_645_, v_val_662_);
if (v___x_671_ == 0)
{
lean_dec(v_val_664_);
lean_dec(v_val_662_);
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
if (lean_obj_tag(v_endPos_x3f_646_) == 0)
{
v___y_666_ = v___x_671_;
goto v___jp_665_;
}
else
{
lean_object* v_val_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_val_672_ = lean_ctor_get(v_endPos_x3f_646_, 0);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_val_662_, v___x_673_);
v___x_675_ = lean_nat_dec_le(v___x_674_, v_val_672_);
lean_dec(v___x_674_);
v___y_666_ = v___x_675_;
goto v___jp_665_;
}
}
v___jp_665_:
{
if (v___y_666_ == 0)
{
lean_dec(v_val_664_);
lean_dec(v_val_662_);
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_inc_ref_n(v_text_644_, 2);
v___x_667_ = l_Lean_FileMap_utf8PosToLspPos(v_text_644_, v_val_662_);
lean_dec(v_val_662_);
v___x_668_ = l_Lean_FileMap_utf8PosToLspPos(v_text_644_, v_val_664_);
lean_dec(v_val_664_);
lean_inc(v_priority_660_);
v___x_669_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_ctor_set(v___x_669_, 2, v_priority_660_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*3, v_type_659_);
v___x_670_ = lean_array_push(v_b_650_, v___x_669_);
v___y_652_ = v___x_670_;
goto v___jp_651_;
}
}
}
}
}
else
{
lean_dec_ref(v_text_644_);
return v_b_650_;
}
v___jp_651_:
{
size_t v___x_653_; size_t v___x_654_; 
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_add(v_i_648_, v___x_653_);
v_i_648_ = v___x_654_;
v_b_650_ = v___y_652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object* v_text_676_, lean_object* v_beginPos_677_, lean_object* v_endPos_x3f_678_, lean_object* v_as_679_, lean_object* v_i_680_, lean_object* v_stop_681_, lean_object* v_b_682_){
_start:
{
size_t v_i_boxed_683_; size_t v_stop_boxed_684_; lean_object* v_res_685_; 
v_i_boxed_683_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_stop_boxed_684_ = lean_unbox_usize(v_stop_681_);
lean_dec(v_stop_681_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_676_, v_beginPos_677_, v_endPos_x3f_678_, v_as_679_, v_i_boxed_683_, v_stop_boxed_684_, v_b_682_);
lean_dec_ref(v_as_679_);
lean_dec(v_endPos_x3f_678_);
lean_dec(v_beginPos_677_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object* v_text_688_, lean_object* v_beginPos_689_, lean_object* v_endPos_x3f_690_, lean_object* v_as_691_, lean_object* v_start_692_, lean_object* v_stop_693_){
_start:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0));
v___x_695_ = lean_nat_dec_lt(v_start_692_, v_stop_693_);
if (v___x_695_ == 0)
{
lean_dec_ref(v_text_688_);
return v___x_694_;
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_array_get_size(v_as_691_);
v___x_697_ = lean_nat_dec_le(v_stop_693_, v___x_696_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; 
v___x_698_ = lean_nat_dec_lt(v_start_692_, v___x_696_);
if (v___x_698_ == 0)
{
lean_dec_ref(v_text_688_);
return v___x_694_;
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_usize_of_nat(v_start_692_);
v___x_700_ = lean_usize_of_nat(v___x_696_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_688_, v_beginPos_689_, v_endPos_x3f_690_, v_as_691_, v___x_699_, v___x_700_, v___x_694_);
return v___x_701_;
}
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_usize_of_nat(v_start_692_);
v___x_703_ = lean_usize_of_nat(v_stop_693_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_688_, v_beginPos_689_, v_endPos_x3f_690_, v_as_691_, v___x_702_, v___x_703_, v___x_694_);
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object* v_text_705_, lean_object* v_beginPos_706_, lean_object* v_endPos_x3f_707_, lean_object* v_as_708_, lean_object* v_start_709_, lean_object* v_stop_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_705_, v_beginPos_706_, v_endPos_x3f_707_, v_as_708_, v_start_709_, v_stop_710_);
lean_dec(v_stop_710_);
lean_dec(v_start_709_);
lean_dec_ref(v_as_708_);
lean_dec(v_endPos_x3f_707_);
lean_dec(v_beginPos_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object* v_text_712_, lean_object* v_beginPos_713_, lean_object* v_endPos_x3f_714_, lean_object* v_tokens_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_array_get_size(v_tokens_715_);
v___x_718_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_712_, v_beginPos_713_, v_endPos_x3f_714_, v_tokens_715_, v___x_716_, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object* v_text_719_, lean_object* v_beginPos_720_, lean_object* v_endPos_x3f_721_, lean_object* v_tokens_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_719_, v_beginPos_720_, v_endPos_x3f_721_, v_tokens_722_);
lean_dec_ref(v_tokens_722_);
lean_dec(v_endPos_x3f_721_);
lean_dec(v_beginPos_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object* v_s_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v_s_732_);
lean_ctor_set(v___x_734_, 1, v_x_733_);
return v___x_734_;
}
else
{
lean_object* v_head_735_; lean_object* v_tail_736_; lean_object* v_tailPos_737_; lean_object* v_tailPos_738_; uint8_t v___x_739_; 
v_head_735_ = lean_ctor_get(v_x_733_, 0);
v_tail_736_ = lean_ctor_get(v_x_733_, 1);
v_tailPos_737_ = lean_ctor_get(v_s_732_, 1);
v_tailPos_738_ = lean_ctor_get(v_head_735_, 1);
v___x_739_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_737_, v_tailPos_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v_s_732_);
lean_ctor_set(v___x_740_, 1, v_x_733_);
return v___x_740_;
}
else
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
lean_inc(v_tail_736_);
lean_inc(v_head_735_);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; lean_object* v_unused_750_; 
v_unused_749_ = lean_ctor_get(v_x_733_, 1);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_x_733_, 0);
lean_dec(v_unused_750_);
v___x_742_ = v_x_733_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_x_733_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_732_, v_tail_736_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_head_735_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object* v_st_751_, lean_object* v_s_752_){
_start:
{
lean_object* v_nonOverlapping_753_; lean_object* v_current_x3f_754_; lean_object* v_surrounding_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v_nonOverlapping_753_ = lean_ctor_get(v_st_751_, 0);
v_current_x3f_754_ = lean_ctor_get(v_st_751_, 1);
v_surrounding_755_ = lean_ctor_get(v_st_751_, 2);
v_isSharedCheck_763_ = !lean_is_exclusive(v_st_751_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v_st_751_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_surrounding_755_);
lean_inc(v_current_x3f_754_);
lean_inc(v_nonOverlapping_753_);
lean_dec(v_st_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_752_, v_surrounding_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 2, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_nonOverlapping_753_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_current_x3f_754_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object* v_t_764_, lean_object* v_soFar_765_){
_start:
{
lean_object* v_tailPos_766_; lean_object* v_priority_767_; lean_object* v_tailPos_768_; lean_object* v_priority_769_; uint8_t v___x_770_; 
v_tailPos_766_ = lean_ctor_get(v_soFar_765_, 1);
v_priority_767_ = lean_ctor_get(v_soFar_765_, 2);
v_tailPos_768_ = lean_ctor_get(v_t_764_, 1);
v_priority_769_ = lean_ctor_get(v_t_764_, 2);
v___x_770_ = lean_nat_dec_lt(v_priority_767_, v_priority_769_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = lean_nat_dec_eq(v_priority_769_, v_priority_767_);
if (v___x_771_ == 0)
{
return v___x_771_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_768_, v_tailPos_766_);
if (v___x_772_ == 0)
{
return v___x_771_;
}
else
{
return v___x_770_;
}
}
}
else
{
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object* v_t_773_, lean_object* v_soFar_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_t_773_, v_soFar_774_);
lean_dec_ref(v_soFar_774_);
lean_dec_ref(v_t_773_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
return v_x_777_;
}
else
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v_head_779_; lean_object* v_tail_780_; lean_object* v___x_781_; 
v_head_779_ = lean_ctor_get(v_x_778_, 0);
v_tail_780_ = lean_ctor_get(v_x_778_, 1);
lean_inc(v_head_779_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v_head_779_);
v_x_777_ = v___x_781_;
v_x_778_ = v_tail_780_;
goto _start;
}
else
{
lean_object* v_head_783_; lean_object* v_tail_784_; lean_object* v_val_785_; uint8_t v___x_786_; 
v_head_783_ = lean_ctor_get(v_x_778_, 0);
v_tail_784_ = lean_ctor_get(v_x_778_, 1);
v_val_785_ = lean_ctor_get(v_x_777_, 0);
v___x_786_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_head_783_, v_val_785_);
if (v___x_786_ == 0)
{
v_x_778_ = v_tail_784_;
goto _start;
}
else
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_isSharedCheck_795_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_x_777_, 0);
lean_dec(v_unused_796_);
v___x_789_ = v_x_777_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_dec(v_x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
lean_inc(v_head_783_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_head_783_);
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_head_783_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v_x_777_ = v___x_792_;
v_x_778_ = v_tail_784_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v_x_797_, v_x_798_);
lean_dec(v_x_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object* v_toks_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_box(0);
v___x_802_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v___x_801_, v_toks_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object* v_toks_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_toks_803_);
lean_dec(v_toks_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object* v_val_805_, lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
return v_x_806_;
}
else
{
lean_object* v_head_807_; lean_object* v_tail_808_; lean_object* v_tailPos_809_; lean_object* v_tailPos_810_; uint8_t v___x_811_; 
v_head_807_ = lean_ctor_get(v_x_806_, 0);
v_tail_808_ = lean_ctor_get(v_x_806_, 1);
v_tailPos_809_ = lean_ctor_get(v_head_807_, 1);
v_tailPos_810_ = lean_ctor_get(v_val_805_, 1);
v___x_811_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_809_, v_tailPos_810_);
if (v___x_811_ == 2)
{
lean_inc_ref(v_x_806_);
return v_x_806_;
}
else
{
v_x_806_ = v_tail_808_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object* v_val_813_, lean_object* v_x_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_813_, v_x_814_);
lean_dec(v_x_814_);
lean_dec_ref(v_val_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object* v_nextToken_x3f_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_current_x3f_818_; 
v_current_x3f_818_ = lean_ctor_get(v_a_817_, 1);
if (lean_obj_tag(v_current_x3f_818_) == 1)
{
lean_object* v_nonOverlapping_819_; lean_object* v_surrounding_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_861_; 
lean_inc_ref(v_current_x3f_818_);
v_nonOverlapping_819_ = lean_ctor_get(v_a_817_, 0);
v_surrounding_820_ = lean_ctor_get(v_a_817_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_a_817_, 1);
lean_dec(v_unused_862_);
v___x_822_ = v_a_817_;
v_isShared_823_ = v_isSharedCheck_861_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_surrounding_820_);
lean_inc(v_nonOverlapping_819_);
lean_dec(v_a_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_861_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_val_824_; lean_object* v___x_825_; lean_object* v___y_827_; lean_object* v___y_828_; 
v_val_824_ = lean_ctor_get(v_current_x3f_818_, 0);
v___x_825_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_824_, v_surrounding_820_);
lean_dec(v_surrounding_820_);
if (lean_obj_tag(v_nextToken_x3f_816_) == 1)
{
lean_object* v_val_856_; lean_object* v_tailPos_857_; lean_object* v_pos_858_; uint8_t v___x_859_; 
v_val_856_ = lean_ctor_get(v_nextToken_x3f_816_, 0);
v_tailPos_857_ = lean_ctor_get(v_val_824_, 1);
v_pos_858_ = lean_ctor_get(v_val_856_, 0);
v___x_859_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_857_, v_pos_858_);
if (v___x_859_ == 2)
{
lean_object* v___x_860_; 
lean_del_object(v___x_822_);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v_nonOverlapping_819_);
lean_ctor_set(v___x_860_, 1, v_current_x3f_818_);
lean_ctor_set(v___x_860_, 2, v___x_825_);
return v___x_860_;
}
else
{
lean_inc(v_val_824_);
lean_dec_ref_known(v_current_x3f_818_, 1);
goto v___jp_833_;
}
}
else
{
lean_inc(v_val_824_);
lean_dec_ref_known(v_current_x3f_818_, 1);
goto v___jp_833_;
}
v___jp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 2, v___x_825_);
lean_ctor_set(v___x_822_, 1, v___y_828_);
lean_ctor_set(v___x_822_, 0, v___y_827_);
v___x_830_ = v___x_822_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___y_827_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___y_828_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v___x_825_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v_a_817_ = v___x_830_;
goto _start;
}
}
v___jp_833_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc(v_val_824_);
v___x_834_ = lean_array_push(v_nonOverlapping_819_, v_val_824_);
v___x_835_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v___x_825_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_dec(v_val_824_);
v___y_827_ = v___x_834_;
v___y_828_ = v___x_835_;
goto v___jp_826_;
}
else
{
lean_object* v_val_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_855_; 
v_val_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_855_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_855_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_val_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_855_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_tailPos_840_; lean_object* v_tailPos_841_; uint8_t v_type_842_; lean_object* v_priority_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_853_; 
v_tailPos_840_ = lean_ctor_get(v_val_824_, 1);
lean_inc_ref(v_tailPos_840_);
lean_dec(v_val_824_);
v_tailPos_841_ = lean_ctor_get(v_val_836_, 1);
v_type_842_ = lean_ctor_get_uint8(v_val_836_, sizeof(void*)*3);
v_priority_843_ = lean_ctor_get(v_val_836_, 2);
v_isSharedCheck_853_ = !lean_is_exclusive(v_val_836_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_val_836_, 0);
lean_dec(v_unused_854_);
v___x_845_ = v_val_836_;
v_isShared_846_ = v_isSharedCheck_853_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_priority_843_);
lean_inc(v_tailPos_841_);
lean_dec(v_val_836_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_853_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v_tailPos_840_);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_tailPos_840_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_tailPos_841_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_priority_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_852_, sizeof(void*)*3, v_type_842_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_848_);
v___x_850_ = v___x_838_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
v___y_827_ = v___x_834_;
v___y_828_ = v___x_850_;
goto v___jp_826_;
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
lean_object* v_nonOverlapping_863_; lean_object* v_surrounding_864_; lean_object* v___x_865_; 
v_nonOverlapping_863_ = lean_ctor_get(v_a_817_, 0);
v_surrounding_864_ = lean_ctor_get(v_a_817_, 2);
v___x_865_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_864_);
if (lean_obj_tag(v___x_865_) == 1)
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
lean_inc(v_surrounding_864_);
lean_inc_ref(v_nonOverlapping_863_);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_874_ = lean_ctor_get(v_a_817_, 2);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_a_817_, 1);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_a_817_, 0);
lean_dec(v_unused_876_);
v___x_867_ = v_a_817_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_a_817_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_865_);
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_nonOverlapping_863_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_surrounding_864_);
v___x_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v_a_817_ = v___x_870_;
goto _start;
}
}
}
else
{
lean_dec(v___x_865_);
return v_a_817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object* v_nextToken_x3f_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_877_, v_a_878_);
lean_dec(v_nextToken_x3f_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_880_, lean_object* v_nextToken_x3f_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_881_, v_st_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object* v_st_883_, lean_object* v_nextToken_x3f_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(v_st_883_, v_nextToken_x3f_884_);
lean_dec(v_nextToken_x3f_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object* v_nextToken_x3f_886_, lean_object* v_inst_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_886_, v_a_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object* v_nextToken_x3f_890_, lean_object* v_inst_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_890_, v_inst_891_, v_a_892_);
lean_dec(v_nextToken_x3f_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_894_, lean_object* v_t_895_){
_start:
{
lean_object* v___x_896_; lean_object* v_st_897_; lean_object* v_current_x3f_898_; 
lean_inc_ref(v_t_895_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_t_895_);
v_st_897_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_896_, v_st_894_);
v_current_x3f_898_ = lean_ctor_get(v_st_897_, 1);
lean_inc(v_current_x3f_898_);
if (lean_obj_tag(v_current_x3f_898_) == 1)
{
lean_object* v_val_899_; lean_object* v_nonOverlapping_900_; lean_object* v_surrounding_901_; lean_object* v_pos_902_; lean_object* v_tailPos_903_; lean_object* v_priority_904_; lean_object* v_pos_905_; lean_object* v_tailPos_906_; uint8_t v_type_907_; lean_object* v_priority_908_; lean_object* v___y_910_; uint8_t v___y_919_; uint8_t v___x_921_; 
v_val_899_ = lean_ctor_get(v_current_x3f_898_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v_current_x3f_898_, 1);
v_nonOverlapping_900_ = lean_ctor_get(v_st_897_, 0);
lean_inc_ref(v_nonOverlapping_900_);
v_surrounding_901_ = lean_ctor_get(v_st_897_, 2);
lean_inc(v_surrounding_901_);
v_pos_902_ = lean_ctor_get(v_t_895_, 0);
v_tailPos_903_ = lean_ctor_get(v_t_895_, 1);
v_priority_904_ = lean_ctor_get(v_t_895_, 2);
v_pos_905_ = lean_ctor_get(v_val_899_, 0);
v_tailPos_906_ = lean_ctor_get(v_val_899_, 1);
v_type_907_ = lean_ctor_get_uint8(v_val_899_, sizeof(void*)*3);
v_priority_908_ = lean_ctor_get(v_val_899_, 2);
v___x_921_ = lean_nat_dec_lt(v_priority_904_, v_priority_908_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; 
v___x_922_ = lean_nat_dec_eq(v_priority_908_, v_priority_904_);
if (v___x_922_ == 0)
{
lean_inc_ref(v_tailPos_903_);
lean_inc_ref(v_pos_902_);
lean_dec_ref(v_st_897_);
lean_dec_ref(v_t_895_);
goto v___jp_914_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_905_, v_pos_902_);
if (v___x_923_ == 0)
{
lean_inc_ref(v_tailPos_903_);
lean_inc_ref(v_pos_902_);
lean_dec_ref(v_st_897_);
lean_dec_ref(v_t_895_);
goto v___jp_914_;
}
else
{
uint8_t v___x_924_; 
v___x_924_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_906_, v_tailPos_903_);
if (v___x_924_ == 0)
{
v___y_919_ = v___x_923_;
goto v___jp_918_;
}
else
{
v___y_919_ = v___x_921_;
goto v___jp_918_;
}
}
}
}
else
{
lean_object* v___x_925_; 
lean_dec(v_surrounding_901_);
lean_dec_ref(v_nonOverlapping_900_);
lean_dec(v_val_899_);
lean_dec_ref_known(v___x_896_, 1);
v___x_925_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_897_, v_t_895_);
return v___x_925_;
}
v___jp_909_:
{
lean_object* v_st_911_; uint8_t v___x_912_; 
v_st_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_911_, 0, v___y_910_);
lean_ctor_set(v_st_911_, 1, v___x_896_);
lean_ctor_set(v_st_911_, 2, v_surrounding_901_);
v___x_912_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_903_, v_tailPos_906_);
lean_dec_ref(v_tailPos_903_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_911_, v_val_899_);
return v___x_913_;
}
else
{
lean_dec(v_val_899_);
return v_st_911_;
}
}
v___jp_914_:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_905_, v_pos_902_);
if (v___x_915_ == 0)
{
lean_object* v_curr_916_; lean_object* v___x_917_; 
lean_inc(v_priority_908_);
lean_inc_ref(v_pos_905_);
v_curr_916_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_916_, 0, v_pos_905_);
lean_ctor_set(v_curr_916_, 1, v_pos_902_);
lean_ctor_set(v_curr_916_, 2, v_priority_908_);
lean_ctor_set_uint8(v_curr_916_, sizeof(void*)*3, v_type_907_);
v___x_917_ = lean_array_push(v_nonOverlapping_900_, v_curr_916_);
v___y_910_ = v___x_917_;
goto v___jp_909_;
}
else
{
lean_dec_ref(v_pos_902_);
v___y_910_ = v_nonOverlapping_900_;
goto v___jp_909_;
}
}
v___jp_918_:
{
if (v___y_919_ == 0)
{
lean_inc_ref(v_tailPos_903_);
lean_inc_ref(v_pos_902_);
lean_dec_ref(v_st_897_);
lean_dec_ref(v_t_895_);
goto v___jp_914_;
}
else
{
lean_object* v___x_920_; 
lean_dec(v_surrounding_901_);
lean_dec_ref(v_nonOverlapping_900_);
lean_dec(v_val_899_);
lean_dec_ref_known(v___x_896_, 1);
v___x_920_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_897_, v_t_895_);
return v___x_920_;
}
}
}
else
{
lean_object* v_nonOverlapping_926_; lean_object* v_surrounding_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_current_x3f_898_);
lean_dec_ref(v_t_895_);
v_nonOverlapping_926_ = lean_ctor_get(v_st_897_, 0);
v_surrounding_927_ = lean_ctor_get(v_st_897_, 2);
v_isSharedCheck_934_ = !lean_is_exclusive(v_st_897_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v_st_897_, 1);
lean_dec(v_unused_935_);
v___x_929_ = v_st_897_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_surrounding_927_);
lean_inc(v_nonOverlapping_926_);
lean_dec(v_st_897_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_896_);
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_nonOverlapping_926_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_surrounding_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_pos_938_; lean_object* v_tailPos_939_; lean_object* v_pos_940_; lean_object* v_tailPos_941_; uint8_t v___y_943_; uint8_t v___x_947_; 
v_pos_938_ = lean_ctor_get(v_x_936_, 0);
v_tailPos_939_ = lean_ctor_get(v_x_936_, 1);
v_pos_940_ = lean_ctor_get(v_x_937_, 0);
v_tailPos_941_ = lean_ctor_get(v_x_937_, 1);
v___x_947_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_939_, v_tailPos_941_);
if (v___x_947_ == 2)
{
uint8_t v___x_948_; 
v___x_948_ = 0;
v___y_943_ = v___x_948_;
goto v___jp_942_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = 1;
v___y_943_ = v___x_949_;
goto v___jp_942_;
}
v___jp_942_:
{
uint8_t v___x_944_; 
v___x_944_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_938_, v_pos_940_);
if (v___x_944_ == 0)
{
uint8_t v___x_945_; 
v___x_945_ = 1;
return v___x_945_;
}
else
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_938_, v_pos_940_);
if (v___x_946_ == 0)
{
return v___x_946_;
}
else
{
return v___y_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_950_, v_x_951_);
lean_dec_ref(v_x_951_);
lean_dec_ref(v_x_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_954_, lean_object* v_b_955_){
_start:
{
if (lean_obj_tag(v_as_x27_954_) == 0)
{
return v_b_955_;
}
else
{
lean_object* v_head_956_; lean_object* v_tail_957_; lean_object* v___x_958_; 
v_head_956_ = lean_ctor_get(v_as_x27_954_, 0);
v_tail_957_ = lean_ctor_get(v_as_x27_954_, 1);
lean_inc(v_head_956_);
v___x_958_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_955_, v_head_956_);
v_as_x27_954_ = v_tail_957_;
v_b_955_ = v___x_958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object* v_as_x27_960_, lean_object* v_b_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_960_, v_b_961_);
lean_dec(v_as_x27_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_964_){
_start:
{
lean_object* v___f_965_; lean_object* v_count_966_; lean_object* v___x_967_; lean_object* v_tokens_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_st_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v_nonOverlapping_979_; 
v___f_965_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_966_ = lean_array_get_size(v_tokens_964_);
v___x_967_ = lean_array_to_list(v_tokens_964_);
v_tokens_968_ = l_List_mergeSort___redArg(v___x_967_, v___f_965_);
v___x_969_ = lean_unsigned_to_nat(11u);
v___x_970_ = lean_nat_mul(v_count_966_, v___x_969_);
v___x_971_ = lean_unsigned_to_nat(10u);
v___x_972_ = lean_nat_div(v___x_970_, v___x_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_mk_empty_array_with_capacity(v___x_972_);
lean_dec(v___x_972_);
v___x_974_ = lean_box(0);
v___x_975_ = lean_box(0);
v_st_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_976_, 0, v___x_973_);
lean_ctor_set(v_st_976_, 1, v___x_974_);
lean_ctor_set(v_st_976_, 2, v___x_975_);
v___x_977_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_968_, v_st_976_);
lean_dec(v_tokens_968_);
v___x_978_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_974_, v___x_977_);
v_nonOverlapping_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_nonOverlapping_979_);
lean_dec_ref(v___x_978_);
return v_nonOverlapping_979_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_980_, lean_object* v_as_x27_981_, lean_object* v_b_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_981_, v_b_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_985_, lean_object* v_as_x27_986_, lean_object* v_b_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_985_, v_as_x27_986_, v_b_987_, v_a_988_);
lean_dec(v_as_x27_986_);
lean_dec(v_as_985_);
return v_res_989_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v_pos_993_; lean_object* v_tailPos_994_; lean_object* v_pos_995_; lean_object* v_tailPos_996_; uint8_t v___y_998_; uint8_t v___x_1001_; 
v_pos_993_ = lean_ctor_get(v_x_991_, 0);
v_tailPos_994_ = lean_ctor_get(v_x_991_, 1);
v_pos_995_ = lean_ctor_get(v_x_992_, 0);
v_tailPos_996_ = lean_ctor_get(v_x_992_, 1);
v___x_1001_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_994_, v_tailPos_996_);
if (v___x_1001_ == 2)
{
uint8_t v___x_1002_; 
v___x_1002_ = 0;
v___y_998_ = v___x_1002_;
goto v___jp_997_;
}
else
{
v___y_998_ = v___x_990_;
goto v___jp_997_;
}
v___jp_997_:
{
uint8_t v___x_999_; 
v___x_999_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_993_, v_pos_995_);
if (v___x_999_ == 0)
{
return v___x_990_;
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_993_, v_pos_995_);
if (v___x_1000_ == 0)
{
return v___x_1000_;
}
else
{
return v___y_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
uint8_t v___x_1122__boxed_1006_; uint8_t v_res_1007_; lean_object* v_r_1008_; 
v___x_1122__boxed_1006_ = lean_unbox(v___x_1003_);
v_res_1007_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1122__boxed_1006_, v_x_1004_, v_x_1005_);
lean_dec_ref(v_x_1005_);
lean_dec_ref(v_x_1004_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object* v_hi_1009_, lean_object* v_pivot_1010_, lean_object* v_as_1011_, lean_object* v_i_1012_, lean_object* v_k_1013_){
_start:
{
uint8_t v___y_1021_; uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_lt(v_k_1013_, v_hi_1009_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec(v_k_1013_);
v___x_1026_ = lean_array_fswap(v_as_1011_, v_i_1012_, v_hi_1009_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_i_1012_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v_pos_1029_; lean_object* v_tailPos_1030_; lean_object* v_pos_1031_; lean_object* v_tailPos_1032_; uint8_t v___y_1034_; uint8_t v___y_1037_; uint8_t v___x_1039_; 
v___x_1028_ = lean_array_fget_borrowed(v_as_1011_, v_k_1013_);
v_pos_1029_ = lean_ctor_get(v___x_1028_, 0);
v_tailPos_1030_ = lean_ctor_get(v___x_1028_, 1);
v_pos_1031_ = lean_ctor_get(v_pivot_1010_, 0);
v_tailPos_1032_ = lean_ctor_get(v_pivot_1010_, 1);
v___x_1039_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_1030_, v_tailPos_1032_);
if (v___x_1039_ == 2)
{
uint8_t v___x_1040_; 
v___x_1040_ = 0;
v___y_1037_ = v___x_1040_;
goto v___jp_1036_;
}
else
{
v___y_1037_ = v___x_1025_;
goto v___jp_1036_;
}
v___jp_1033_:
{
uint8_t v___x_1035_; 
v___x_1035_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_1029_, v_pos_1031_);
if (v___x_1035_ == 0)
{
v___y_1021_ = v___x_1035_;
goto v___jp_1020_;
}
else
{
v___y_1021_ = v___y_1034_;
goto v___jp_1020_;
}
}
v___jp_1036_:
{
uint8_t v___x_1038_; 
v___x_1038_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_1029_, v_pos_1031_);
if (v___x_1038_ == 0)
{
if (v___x_1025_ == 0)
{
v___y_1034_ = v___y_1037_;
goto v___jp_1033_;
}
else
{
goto v___jp_1014_;
}
}
else
{
v___y_1034_ = v___y_1037_;
goto v___jp_1033_;
}
}
}
v___jp_1014_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = lean_array_fswap(v_as_1011_, v_i_1012_, v_k_1013_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_i_1012_, v___x_1016_);
lean_dec(v_i_1012_);
v___x_1018_ = lean_nat_add(v_k_1013_, v___x_1016_);
lean_dec(v_k_1013_);
v_as_1011_ = v___x_1015_;
v_i_1012_ = v___x_1017_;
v_k_1013_ = v___x_1018_;
goto _start;
}
v___jp_1020_:
{
if (v___y_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_add(v_k_1013_, v___x_1022_);
lean_dec(v_k_1013_);
v_k_1013_ = v___x_1023_;
goto _start;
}
else
{
goto v___jp_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1041_, lean_object* v_pivot_1042_, lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_k_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1041_, v_pivot_1042_, v_as_1043_, v_i_1044_, v_k_1045_);
lean_dec_ref(v_pivot_1042_);
lean_dec(v_hi_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1047_, lean_object* v_as_1048_, lean_object* v_lo_1049_, lean_object* v_hi_1050_){
_start:
{
lean_object* v___y_1052_; uint8_t v___x_1062_; 
v___x_1062_ = lean_nat_dec_lt(v_lo_1049_, v_hi_1050_);
if (v___x_1062_ == 0)
{
lean_dec(v_lo_1049_);
return v_as_1048_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_mid_1065_; lean_object* v___y_1067_; lean_object* v___y_1073_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1063_ = lean_nat_add(v_lo_1049_, v_hi_1050_);
v___x_1064_ = lean_unsigned_to_nat(1u);
v_mid_1065_ = lean_nat_shiftr(v___x_1063_, v___x_1064_);
lean_dec(v___x_1063_);
v___x_1078_ = lean_array_fget_borrowed(v_as_1048_, v_mid_1065_);
v___x_1079_ = lean_array_fget_borrowed(v_as_1048_, v_lo_1049_);
v___x_1080_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1062_, v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
v___y_1073_ = v_as_1048_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_array_fswap(v_as_1048_, v_lo_1049_, v_mid_1065_);
v___y_1073_ = v___x_1081_;
goto v___jp_1072_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = lean_array_fget_borrowed(v___y_1067_, v_mid_1065_);
v___x_1069_ = lean_array_fget_borrowed(v___y_1067_, v_hi_1050_);
v___x_1070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1062_, v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v_mid_1065_);
v___y_1052_ = v___y_1067_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_array_fswap(v___y_1067_, v_mid_1065_, v_hi_1050_);
lean_dec(v_mid_1065_);
v___y_1052_ = v___x_1071_;
goto v___jp_1051_;
}
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_array_fget_borrowed(v___y_1073_, v_hi_1050_);
v___x_1075_ = lean_array_fget_borrowed(v___y_1073_, v_lo_1049_);
v___x_1076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1062_, v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
v___y_1067_ = v___y_1073_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_array_fswap(v___y_1073_, v_lo_1049_, v_hi_1050_);
v___y_1067_ = v___x_1077_;
goto v___jp_1066_;
}
}
}
v___jp_1051_:
{
lean_object* v_pivot_1053_; lean_object* v___x_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; uint8_t v___x_1057_; 
v_pivot_1053_ = lean_array_fget(v___y_1052_, v_hi_1050_);
lean_inc_n(v_lo_1049_, 2);
v___x_1054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1050_, v_pivot_1053_, v___y_1052_, v_lo_1049_, v_lo_1049_);
lean_dec(v_pivot_1053_);
v_fst_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_fst_1055_);
v_snd_1056_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_snd_1056_);
lean_dec_ref(v___x_1054_);
v___x_1057_ = lean_nat_dec_le(v_hi_1050_, v_fst_1055_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1047_, v_snd_1056_, v_lo_1049_, v_fst_1055_);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_fst_1055_, v___x_1059_);
lean_dec(v_fst_1055_);
v_as_1048_ = v___x_1058_;
v_lo_1049_ = v___x_1060_;
goto _start;
}
else
{
lean_dec(v_fst_1055_);
lean_dec(v_lo_1049_);
return v_snd_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1082_, lean_object* v_as_1083_, lean_object* v_lo_1084_, lean_object* v_hi_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1082_, v_as_1083_, v_lo_1084_, v_hi_1085_);
lean_dec(v_hi_1085_);
lean_dec(v_n_1082_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1087_, size_t v_sz_1088_, size_t v_i_1089_, lean_object* v_b_1090_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_usize_dec_lt(v_i_1089_, v_sz_1088_);
if (v___x_1091_ == 0)
{
return v_b_1090_;
}
else
{
lean_object* v_a_1092_; lean_object* v_pos_1093_; lean_object* v_snd_1094_; lean_object* v_tailPos_1095_; uint8_t v_type_1096_; lean_object* v_fst_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1128_; 
v_a_1092_ = lean_array_uget_borrowed(v_as_1087_, v_i_1089_);
v_pos_1093_ = lean_ctor_get(v_a_1092_, 0);
v_snd_1094_ = lean_ctor_get(v_b_1090_, 1);
lean_inc(v_snd_1094_);
v_tailPos_1095_ = lean_ctor_get(v_a_1092_, 1);
v_type_1096_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3);
v_fst_1097_ = lean_ctor_get(v_b_1090_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_b_1090_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_b_1090_, 1);
lean_dec(v_unused_1129_);
v___x_1099_ = v_b_1090_;
v_isShared_1100_ = v_isSharedCheck_1128_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_fst_1097_);
lean_dec(v_b_1090_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1128_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_line_1101_; lean_object* v_character_1102_; lean_object* v_line_1103_; lean_object* v_character_1104_; lean_object* v_tokenModifiers_1105_; lean_object* v___x_1106_; lean_object* v___y_1108_; uint8_t v___x_1127_; 
v_line_1101_ = lean_ctor_get(v_pos_1093_, 0);
v_character_1102_ = lean_ctor_get(v_pos_1093_, 1);
v_line_1103_ = lean_ctor_get(v_snd_1094_, 0);
lean_inc(v_line_1103_);
v_character_1104_ = lean_ctor_get(v_snd_1094_, 1);
lean_inc(v_character_1104_);
lean_dec(v_snd_1094_);
v_tokenModifiers_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_nat_sub(v_line_1101_, v_line_1103_);
v___x_1127_ = lean_nat_dec_eq(v_line_1101_, v_line_1103_);
lean_dec(v_line_1103_);
if (v___x_1127_ == 0)
{
lean_dec(v_character_1104_);
v___y_1108_ = v_tokenModifiers_1105_;
goto v___jp_1107_;
}
else
{
v___y_1108_ = v_character_1104_;
goto v___jp_1107_;
}
v___jp_1107_:
{
lean_object* v_character_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v_character_1109_ = lean_ctor_get(v_tailPos_1095_, 1);
v___x_1110_ = lean_nat_sub(v_character_1102_, v___y_1108_);
lean_dec(v___y_1108_);
v___x_1111_ = lean_nat_sub(v_character_1109_, v_character_1102_);
v___x_1112_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1096_);
v___x_1113_ = lean_unsigned_to_nat(5u);
v___x_1114_ = lean_mk_empty_array_with_capacity(v___x_1113_);
v___x_1115_ = lean_array_push(v___x_1114_, v___x_1106_);
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1110_);
v___x_1117_ = lean_array_push(v___x_1116_, v___x_1111_);
v___x_1118_ = lean_array_push(v___x_1117_, v___x_1112_);
v___x_1119_ = lean_array_push(v___x_1118_, v_tokenModifiers_1105_);
v___x_1120_ = l_Array_append___redArg(v_fst_1097_, v___x_1119_);
lean_dec_ref(v___x_1119_);
lean_inc_ref(v_pos_1093_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v_pos_1093_);
lean_ctor_set(v___x_1099_, 0, v___x_1120_);
v___x_1122_ = v___x_1099_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_pos_1093_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
size_t v___x_1123_; size_t v___x_1124_; 
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_add(v_i_1089_, v___x_1123_);
v_i_1089_ = v___x_1124_;
v_b_1090_ = v___x_1122_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1130_, lean_object* v_sz_1131_, lean_object* v_i_1132_, lean_object* v_b_1133_){
_start:
{
size_t v_sz_boxed_1134_; size_t v_i_boxed_1135_; lean_object* v_res_1136_; 
v_sz_boxed_1134_ = lean_unbox_usize(v_sz_1131_);
lean_dec(v_sz_1131_);
v_i_boxed_1135_ = lean_unbox_usize(v_i_1132_);
lean_dec(v_i_1132_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1130_, v_sz_boxed_1134_, v_i_boxed_1135_, v_b_1133_);
lean_dec_ref(v_as_1130_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1139_){
_start:
{
lean_object* v_tokenModifiers_1140_; lean_object* v___y_1142_; lean_object* v___x_1162_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v___x_1167_; 
v_tokenModifiers_1140_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_array_get_size(v_tokens_1139_);
v___x_1167_ = lean_nat_dec_eq(v___x_1162_, v_tokenModifiers_1140_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___y_1171_; uint8_t v___x_1173_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_nat_sub(v___x_1162_, v___x_1168_);
v___x_1173_ = lean_nat_dec_le(v_tokenModifiers_1140_, v___x_1169_);
if (v___x_1173_ == 0)
{
lean_inc(v___x_1169_);
v___y_1171_ = v___x_1169_;
goto v___jp_1170_;
}
else
{
v___y_1171_ = v_tokenModifiers_1140_;
goto v___jp_1170_;
}
v___jp_1170_:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_nat_dec_le(v___y_1171_, v___x_1169_);
if (v___x_1172_ == 0)
{
lean_dec(v___x_1169_);
lean_inc(v___y_1171_);
v___y_1164_ = v___y_1171_;
v___y_1165_ = v___y_1171_;
goto v___jp_1163_;
}
else
{
v___y_1164_ = v___y_1171_;
v___y_1165_ = v___x_1169_;
goto v___jp_1163_;
}
}
}
else
{
v___y_1142_ = v_tokens_1139_;
goto v___jp_1141_;
}
v___jp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v_data_1146_; lean_object* v_lastPos_1147_; lean_object* v___x_1148_; size_t v_sz_1149_; size_t v___x_1150_; lean_object* v___x_1151_; lean_object* v_fst_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v___x_1143_ = lean_unsigned_to_nat(5u);
v___x_1144_ = lean_array_get_size(v___y_1142_);
v___x_1145_ = lean_nat_mul(v___x_1143_, v___x_1144_);
v_data_1146_ = lean_mk_empty_array_with_capacity(v___x_1145_);
lean_dec(v___x_1145_);
v_lastPos_1147_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_data_1146_);
lean_ctor_set(v___x_1148_, 1, v_lastPos_1147_);
v_sz_1149_ = lean_array_size(v___y_1142_);
v___x_1150_ = ((size_t)0ULL);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1142_, v_sz_1149_, v___x_1150_, v___x_1148_);
lean_dec_ref(v___y_1142_);
v_fst_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1151_, 1);
lean_dec(v_unused_1161_);
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_fst_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_box(0);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_fst_1152_);
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_fst_1152_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
v___jp_1163_:
{
lean_object* v___x_1166_; 
v___x_1166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1162_, v_tokens_1139_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
v___y_1142_ = v___x_1166_;
goto v___jp_1141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1174_, lean_object* v_as_1175_, lean_object* v_lo_1176_, lean_object* v_hi_1177_, lean_object* v_w_1178_, lean_object* v_hlo_1179_, lean_object* v_hhi_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1174_, v_as_1175_, v_lo_1176_, v_hi_1177_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1182_, lean_object* v_as_1183_, lean_object* v_lo_1184_, lean_object* v_hi_1185_, lean_object* v_w_1186_, lean_object* v_hlo_1187_, lean_object* v_hhi_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1182_, v_as_1183_, v_lo_1184_, v_hi_1185_, v_w_1186_, v_hlo_1187_, v_hhi_1188_);
lean_dec(v_hi_1185_);
lean_dec(v_n_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1190_, lean_object* v_lo_1191_, lean_object* v_hi_1192_, lean_object* v_hhi_1193_, lean_object* v_pivot_1194_, lean_object* v_as_1195_, lean_object* v_i_1196_, lean_object* v_k_1197_, lean_object* v_ilo_1198_, lean_object* v_ik_1199_, lean_object* v_w_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1192_, v_pivot_1194_, v_as_1195_, v_i_1196_, v_k_1197_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1202_, lean_object* v_lo_1203_, lean_object* v_hi_1204_, lean_object* v_hhi_1205_, lean_object* v_pivot_1206_, lean_object* v_as_1207_, lean_object* v_i_1208_, lean_object* v_k_1209_, lean_object* v_ilo_1210_, lean_object* v_ik_1211_, lean_object* v_w_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1202_, v_lo_1203_, v_hi_1204_, v_hhi_1205_, v_pivot_1206_, v_as_1207_, v_i_1208_, v_k_1209_, v_ilo_1210_, v_ik_1211_, v_w_1212_);
lean_dec_ref(v_pivot_1206_);
lean_dec(v_hi_1204_);
lean_dec(v_lo_1203_);
lean_dec(v_n_1202_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1214_, uint8_t v_k_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___y_1218_; 
if (v_k_1215_ == 18)
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_unsigned_to_nat(3u);
v___y_1218_ = v___x_1223_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_unsigned_to_nat(5u);
v___y_1218_ = v___x_1224_;
goto v___jp_1217_;
}
v___jp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1220_, 0, v_tk_1214_);
lean_ctor_set(v___x_1220_, 1, v___y_1218_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*2, v_k_1215_);
v___x_1221_ = lean_array_push(v_a_1216_, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1219_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1225_, lean_object* v_k_1226_, lean_object* v_a_1227_){
_start:
{
uint8_t v_k_boxed_1228_; lean_object* v_res_1229_; 
v_k_boxed_1228_ = lean_unbox(v_k_1226_);
v_res_1229_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1225_, v_k_boxed_1228_, v_a_1227_);
return v_res_1229_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_1232_ = lean_string_utf8_byte_size(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(lean_object* v_text_1233_, lean_object* v_line_1234_){
_start:
{
uint8_t v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = 0;
v___x_1236_ = l_Lean_Syntax_getRange_x3f(v_line_1234_, v___x_1235_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_box(0);
return v___x_1237_;
}
else
{
lean_object* v_val_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1275_; 
v_val_1238_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1240_ = v___x_1236_;
v_isShared_1241_ = v_isSharedCheck_1275_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_val_1238_);
lean_dec(v___x_1236_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1275_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_start_1242_; lean_object* v_stop_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1274_; 
v_start_1242_ = lean_ctor_get(v_val_1238_, 0);
v_stop_1243_ = lean_ctor_get(v_val_1238_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_val_1238_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1245_ = v_val_1238_;
v_isShared_1246_ = v_isSharedCheck_1274_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_stop_1243_);
lean_inc(v_start_1242_);
lean_dec(v_val_1238_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1274_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
uint8_t v___y_1248_; lean_object* v___y_1249_; uint8_t v___y_1262_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1266_ = l_Lean_TSyntax_getVersoCodeBlockLine(v_line_1234_);
v___x_1267_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_1268_ = lean_string_utf8_byte_size(v___x_1266_);
v___x_1269_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1, &l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1_once, _init_l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1);
v___x_1270_ = lean_nat_dec_le(v___x_1269_, v___x_1268_);
if (v___x_1270_ == 0)
{
lean_dec_ref(v___x_1266_);
v___y_1262_ = v___x_1270_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_nat_sub(v___x_1268_, v___x_1269_);
v___x_1273_ = lean_string_memcmp(v___x_1266_, v___x_1267_, v___x_1272_, v___x_1271_, v___x_1269_);
lean_dec(v___x_1272_);
lean_dec_ref(v___x_1266_);
v___y_1262_ = v___x_1273_;
goto v___jp_1261_;
}
v___jp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_start_1242_, v___x_1250_);
v___x_1252_ = lean_nat_dec_le(v___x_1251_, v___y_1249_);
lean_dec(v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v___y_1249_);
lean_del_object(v___x_1245_);
lean_dec(v_start_1242_);
lean_del_object(v___x_1240_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
else
{
lean_object* v___x_1255_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___y_1249_);
v___x_1255_ = v___x_1245_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_start_1242_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___y_1249_);
v___x_1255_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = l_Lean_Syntax_ofRange(v___x_1255_, v___y_1248_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1256_);
v___x_1258_ = v___x_1240_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
v___jp_1261_:
{
uint8_t v___x_1263_; 
v___x_1263_ = 1;
if (v___y_1262_ == 0)
{
v___y_1248_ = v___x_1263_;
v___y_1249_ = v_stop_1243_;
goto v___jp_1247_;
}
else
{
lean_object* v_source_1264_; lean_object* v___x_1265_; 
v_source_1264_ = lean_ctor_get(v_text_1233_, 0);
v___x_1265_ = lean_string_utf8_prev(v_source_1264_, v_stop_1243_);
lean_dec(v_stop_1243_);
v___y_1248_ = v___x_1263_;
v___y_1249_ = v___x_1265_;
goto v___jp_1247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___boxed(lean_object* v_text_1276_, lean_object* v_line_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_text_1276_, v_line_1277_);
lean_dec(v_line_1277_);
lean_dec_ref(v_text_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goVal(lean_object* v_val_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Doc_ArgValView_of(v_val_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_box(0);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v_a_1280_);
return v___x_1283_;
}
else
{
lean_object* v_val_1284_; lean_object* v_lit_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; 
v_val_1284_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1284_);
lean_dec_ref_known(v___x_1281_, 1);
v_lit_1285_ = lean_ctor_get(v_val_1284_, 0);
lean_inc(v_lit_1285_);
lean_dec(v_val_1284_);
v___x_1286_ = 11;
v___x_1287_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_lit_1285_, v___x_1286_, v_a_1280_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(lean_object* v_arg_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_Doc_ArgView_of(v_arg_1288_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_a_1289_);
return v___x_1292_;
}
else
{
lean_object* v_val_1293_; 
v_val_1293_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v___x_1290_, 1);
switch(lean_obj_tag(v_val_1293_))
{
case 0:
{
lean_object* v_val_1294_; lean_object* v___x_1295_; 
v_val_1294_ = lean_ctor_get(v_val_1293_, 1);
lean_inc(v_val_1294_);
lean_dec_ref_known(v_val_1293_, 2);
v___x_1295_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goVal(v_val_1294_, v_a_1289_);
return v___x_1295_;
}
case 1:
{
lean_object* v_parens_1296_; 
v_parens_1296_ = lean_ctor_get(v_val_1293_, 1);
if (lean_obj_tag(v_parens_1296_) == 0)
{
lean_object* v_name_1297_; lean_object* v_assign_1298_; lean_object* v_val_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v_snd_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v_snd_1305_; lean_object* v___x_1306_; 
v_name_1297_ = lean_ctor_get(v_val_1293_, 2);
lean_inc(v_name_1297_);
v_assign_1298_ = lean_ctor_get(v_val_1293_, 3);
lean_inc(v_assign_1298_);
v_val_1299_ = lean_ctor_get(v_val_1293_, 4);
lean_inc(v_val_1299_);
lean_dec_ref_known(v_val_1293_, 5);
v___x_1300_ = 2;
v___x_1301_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1297_, v___x_1300_, v_a_1289_);
v_snd_1302_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_snd_1302_);
lean_dec_ref(v___x_1301_);
v___x_1303_ = 0;
v___x_1304_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_assign_1298_, v___x_1303_, v_snd_1302_);
v_snd_1305_ = lean_ctor_get(v___x_1304_, 1);
lean_inc(v_snd_1305_);
lean_dec_ref(v___x_1304_);
v___x_1306_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goVal(v_val_1299_, v_snd_1305_);
return v___x_1306_;
}
else
{
lean_object* v_val_1307_; lean_object* v_name_1308_; lean_object* v_assign_1309_; lean_object* v_val_1310_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v_snd_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v_snd_1318_; lean_object* v___x_1319_; lean_object* v_snd_1320_; lean_object* v___x_1321_; lean_object* v_snd_1322_; lean_object* v___x_1323_; 
v_val_1307_ = lean_ctor_get(v_parens_1296_, 0);
lean_inc(v_val_1307_);
v_name_1308_ = lean_ctor_get(v_val_1293_, 2);
lean_inc(v_name_1308_);
v_assign_1309_ = lean_ctor_get(v_val_1293_, 3);
lean_inc(v_assign_1309_);
v_val_1310_ = lean_ctor_get(v_val_1293_, 4);
lean_inc(v_val_1310_);
lean_dec_ref_known(v_val_1293_, 5);
v_fst_1311_ = lean_ctor_get(v_val_1307_, 0);
lean_inc(v_fst_1311_);
v_snd_1312_ = lean_ctor_get(v_val_1307_, 1);
lean_inc(v_snd_1312_);
lean_dec(v_val_1307_);
v___x_1313_ = 0;
v___x_1314_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1311_, v___x_1313_, v_a_1289_);
v_snd_1315_ = lean_ctor_get(v___x_1314_, 1);
lean_inc(v_snd_1315_);
lean_dec_ref(v___x_1314_);
v___x_1316_ = 2;
v___x_1317_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1308_, v___x_1316_, v_snd_1315_);
v_snd_1318_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_snd_1318_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_assign_1309_, v___x_1313_, v_snd_1318_);
v_snd_1320_ = lean_ctor_get(v___x_1319_, 1);
lean_inc(v_snd_1320_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goVal(v_val_1310_, v_snd_1320_);
v_snd_1322_ = lean_ctor_get(v___x_1321_, 1);
lean_inc(v_snd_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1312_, v___x_1313_, v_snd_1322_);
return v___x_1323_;
}
}
default: 
{
lean_object* v_sign_1324_; lean_object* v_name_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v_snd_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; 
v_sign_1324_ = lean_ctor_get(v_val_1293_, 1);
lean_inc(v_sign_1324_);
v_name_1325_ = lean_ctor_get(v_val_1293_, 2);
lean_inc(v_name_1325_);
lean_dec_ref_known(v_val_1293_, 3);
v___x_1326_ = 0;
v___x_1327_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_sign_1324_, v___x_1326_, v_a_1289_);
v_snd_1328_ = lean_ctor_get(v___x_1327_, 1);
lean_inc(v_snd_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = 2;
v___x_1330_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1325_, v___x_1329_, v_snd_1328_);
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(lean_object* v_tgt_1331_, lean_object* v_a_1332_){
_start:
{
if (lean_obj_tag(v_tgt_1331_) == 0)
{
lean_object* v_opener_1333_; lean_object* v_url_1334_; lean_object* v_closer_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v_snd_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v_snd_1341_; lean_object* v___x_1342_; 
v_opener_1333_ = lean_ctor_get(v_tgt_1331_, 1);
lean_inc(v_opener_1333_);
v_url_1334_ = lean_ctor_get(v_tgt_1331_, 2);
lean_inc(v_url_1334_);
v_closer_1335_ = lean_ctor_get(v_tgt_1331_, 3);
lean_inc(v_closer_1335_);
lean_dec_ref_known(v_tgt_1331_, 4);
v___x_1336_ = 0;
v___x_1337_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1333_, v___x_1336_, v_a_1332_);
v_snd_1338_ = lean_ctor_get(v___x_1337_, 1);
lean_inc(v_snd_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = 18;
v___x_1340_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1334_, v___x_1339_, v_snd_1338_);
v_snd_1341_ = lean_ctor_get(v___x_1340_, 1);
lean_inc(v_snd_1341_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1335_, v___x_1336_, v_snd_1341_);
return v___x_1342_;
}
else
{
lean_object* v_opener_1343_; lean_object* v_name_1344_; lean_object* v_closer_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v_snd_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v_snd_1351_; lean_object* v___x_1352_; 
v_opener_1343_ = lean_ctor_get(v_tgt_1331_, 1);
lean_inc(v_opener_1343_);
v_name_1344_ = lean_ctor_get(v_tgt_1331_, 2);
lean_inc(v_name_1344_);
v_closer_1345_ = lean_ctor_get(v_tgt_1331_, 3);
lean_inc(v_closer_1345_);
lean_dec_ref_known(v_tgt_1331_, 4);
v___x_1346_ = 0;
v___x_1347_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1343_, v___x_1346_, v_a_1332_);
v_snd_1348_ = lean_ctor_get(v___x_1347_, 1);
lean_inc(v_snd_1348_);
lean_dec_ref(v___x_1347_);
v___x_1349_ = 2;
v___x_1350_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1344_, v___x_1349_, v_snd_1348_);
v_snd_1351_ = lean_ctor_get(v___x_1350_, 1);
lean_inc(v_snd_1351_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1345_, v___x_1346_, v_snd_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(lean_object* v_code_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_opener_1355_; lean_object* v_content_1356_; lean_object* v_closer_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v_snd_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; lean_object* v_snd_1363_; lean_object* v___x_1364_; 
v_opener_1355_ = lean_ctor_get(v_code_1353_, 1);
lean_inc(v_opener_1355_);
v_content_1356_ = lean_ctor_get(v_code_1353_, 2);
lean_inc(v_content_1356_);
v_closer_1357_ = lean_ctor_get(v_code_1353_, 3);
lean_inc(v_closer_1357_);
lean_dec_ref(v_code_1353_);
v___x_1358_ = 0;
v___x_1359_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1355_, v___x_1358_, v_a_1354_);
v_snd_1360_ = lean_ctor_get(v___x_1359_, 1);
lean_inc(v_snd_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = 18;
v___x_1362_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_content_1356_, v___x_1361_, v_snd_1360_);
v_snd_1363_ = lean_ctor_get(v___x_1362_, 1);
lean_inc(v_snd_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1357_, v___x_1358_, v_snd_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__7(lean_object* v_text_1365_, lean_object* v_as_1366_, size_t v_sz_1367_, size_t v_i_1368_, lean_object* v_b_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_a_1372_; lean_object* v_snd_1373_; uint8_t v___x_1377_; 
v___x_1377_ = lean_usize_dec_lt(v_i_1368_, v_sz_1367_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_b_1369_);
lean_ctor_set(v___x_1378_, 1, v___y_1370_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v_a_1380_; lean_object* v___x_1381_; 
v___x_1379_ = lean_box(0);
v_a_1380_ = lean_array_uget_borrowed(v_as_1366_, v_i_1368_);
v___x_1381_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_text_1365_, v_a_1380_);
if (lean_obj_tag(v___x_1381_) == 1)
{
lean_object* v_val_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v_snd_1385_; 
v_val_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = 18;
v___x_1384_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1382_, v___x_1383_, v___y_1370_);
v_snd_1385_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_snd_1385_);
lean_dec_ref(v___x_1384_);
v_a_1372_ = v___x_1379_;
v_snd_1373_ = v_snd_1385_;
goto v___jp_1371_;
}
else
{
lean_dec(v___x_1381_);
v_a_1372_ = v___x_1379_;
v_snd_1373_ = v___y_1370_;
goto v___jp_1371_;
}
}
v___jp_1371_:
{
size_t v___x_1374_; size_t v___x_1375_; 
v___x_1374_ = ((size_t)1ULL);
v___x_1375_ = lean_usize_add(v_i_1368_, v___x_1374_);
v_i_1368_ = v___x_1375_;
v_b_1369_ = v_a_1372_;
v___y_1370_ = v_snd_1373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__7___boxed(lean_object* v_text_1386_, lean_object* v_as_1387_, lean_object* v_sz_1388_, lean_object* v_i_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_){
_start:
{
size_t v_sz_boxed_1392_; size_t v_i_boxed_1393_; lean_object* v_res_1394_; 
v_sz_boxed_1392_ = lean_unbox_usize(v_sz_1388_);
lean_dec(v_sz_1388_);
v_i_boxed_1393_ = lean_unbox_usize(v_i_1389_);
lean_dec(v_i_1389_);
v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__7(v_text_1386_, v_as_1387_, v_sz_boxed_1392_, v_i_boxed_1393_, v_b_1390_, v___y_1391_);
lean_dec_ref(v_as_1387_);
lean_dec_ref(v_text_1386_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(lean_object* v_as_1395_, size_t v_sz_1396_, size_t v_i_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v___x_1400_; 
v___x_1400_ = lean_usize_dec_lt(v_i_1397_, v_sz_1396_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_b_1398_);
lean_ctor_set(v___x_1401_, 1, v___y_1399_);
return v___x_1401_;
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1403_; lean_object* v_snd_1404_; lean_object* v___x_1405_; size_t v___x_1406_; size_t v___x_1407_; 
v_a_1402_ = lean_array_uget_borrowed(v_as_1395_, v_i_1397_);
lean_inc(v_a_1402_);
v___x_1403_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(v_a_1402_, v___y_1399_);
v_snd_1404_ = lean_ctor_get(v___x_1403_, 1);
lean_inc(v_snd_1404_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = lean_box(0);
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_add(v_i_1397_, v___x_1406_);
v_i_1397_ = v___x_1407_;
v_b_1398_ = v___x_1405_;
v___y_1399_ = v_snd_1404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3___boxed(lean_object* v_as_1409_, lean_object* v_sz_1410_, lean_object* v_i_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_){
_start:
{
size_t v_sz_boxed_1414_; size_t v_i_boxed_1415_; lean_object* v_res_1416_; 
v_sz_boxed_1414_ = lean_unbox_usize(v_sz_1410_);
lean_dec(v_sz_1410_);
v_i_boxed_1415_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_res_1416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_as_1409_, v_sz_boxed_1414_, v_i_boxed_1415_, v_b_1412_, v___y_1413_);
lean_dec_ref(v_as_1409_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(lean_object* v_text_1417_, lean_object* v_getTokens_1418_, lean_object* v_as_1419_, size_t v_sz_1420_, size_t v_i_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_usize_dec_lt(v_i_1421_, v_sz_1420_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; 
lean_dec_ref(v_getTokens_1418_);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_b_1422_);
lean_ctor_set(v___x_1425_, 1, v___y_1423_);
return v___x_1425_;
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v_snd_1428_; lean_object* v___x_1429_; size_t v___x_1430_; size_t v___x_1431_; 
v_a_1426_ = lean_array_uget_borrowed(v_as_1419_, v_i_1421_);
lean_inc(v_a_1426_);
lean_inc_ref(v_getTokens_1418_);
v___x_1427_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1417_, v_getTokens_1418_, v_a_1426_, v___y_1423_);
v_snd_1428_ = lean_ctor_get(v___x_1427_, 1);
lean_inc(v_snd_1428_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = lean_box(0);
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1421_, v___x_1430_);
v_i_1421_ = v___x_1431_;
v_b_1422_ = v___x_1429_;
v___y_1423_ = v_snd_1428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem(lean_object* v_text_1433_, lean_object* v_getTokens_1434_, lean_object* v_item_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_marker_1437_; lean_object* v_contents_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v_snd_1441_; lean_object* v___x_1442_; size_t v_sz_1443_; size_t v___x_1444_; lean_object* v___x_1445_; lean_object* v_snd_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_marker_1437_ = lean_ctor_get(v_item_1435_, 1);
lean_inc(v_marker_1437_);
v_contents_1438_ = lean_ctor_get(v_item_1435_, 2);
lean_inc_ref(v_contents_1438_);
lean_dec_ref(v_item_1435_);
v___x_1439_ = 0;
v___x_1440_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1437_, v___x_1439_, v_a_1436_);
v_snd_1441_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_snd_1441_);
lean_dec_ref(v___x_1440_);
v___x_1442_ = lean_box(0);
v_sz_1443_ = lean_array_size(v_contents_1438_);
v___x_1444_ = ((size_t)0ULL);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1433_, v_getTokens_1434_, v_contents_1438_, v_sz_1443_, v___x_1444_, v___x_1442_, v_snd_1441_);
lean_dec_ref(v_contents_1438_);
v_snd_1446_ = lean_ctor_get(v___x_1445_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1454_);
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_snd_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1442_);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_snd_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(lean_object* v_text_1455_, lean_object* v_getTokens_1456_, lean_object* v_as_1457_, size_t v_sz_1458_, size_t v_i_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_lt(v_i_1459_, v_sz_1458_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec_ref(v_getTokens_1456_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1460_);
lean_ctor_set(v___x_1463_, 1, v___y_1461_);
return v___x_1463_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v_snd_1466_; lean_object* v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; 
v_a_1464_ = lean_array_uget_borrowed(v_as_1457_, v_i_1459_);
lean_inc(v_a_1464_);
lean_inc_ref(v_getTokens_1456_);
v___x_1465_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem(v_text_1455_, v_getTokens_1456_, v_a_1464_, v___y_1461_);
v_snd_1466_ = lean_ctor_get(v___x_1465_, 1);
lean_inc(v_snd_1466_);
lean_dec_ref(v___x_1465_);
v___x_1467_ = lean_box(0);
v___x_1468_ = ((size_t)1ULL);
v___x_1469_ = lean_usize_add(v_i_1459_, v___x_1468_);
v_i_1459_ = v___x_1469_;
v_b_1460_ = v___x_1467_;
v___y_1461_ = v_snd_1466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goOrderedItem(lean_object* v_text_1471_, lean_object* v_getTokens_1472_, lean_object* v_item_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_marker_1475_; lean_object* v_contents_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v_snd_1479_; lean_object* v___x_1480_; size_t v_sz_1481_; size_t v___x_1482_; lean_object* v___x_1483_; lean_object* v_snd_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_marker_1475_ = lean_ctor_get(v_item_1473_, 1);
lean_inc(v_marker_1475_);
v_contents_1476_ = lean_ctor_get(v_item_1473_, 2);
lean_inc_ref(v_contents_1476_);
lean_dec_ref(v_item_1473_);
v___x_1477_ = 0;
v___x_1478_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1475_, v___x_1477_, v_a_1474_);
v_snd_1479_ = lean_ctor_get(v___x_1478_, 1);
lean_inc(v_snd_1479_);
lean_dec_ref(v___x_1478_);
v___x_1480_ = lean_box(0);
v_sz_1481_ = lean_array_size(v_contents_1476_);
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1471_, v_getTokens_1472_, v_contents_1476_, v_sz_1481_, v___x_1482_, v___x_1480_, v_snd_1479_);
lean_dec_ref(v_contents_1476_);
v_snd_1484_ = lean_ctor_get(v___x_1483_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v___x_1483_, 0);
lean_dec(v_unused_1492_);
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snd_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1480_);
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_snd_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(lean_object* v_text_1493_, lean_object* v_getTokens_1494_, lean_object* v_as_1495_, size_t v_sz_1496_, size_t v_i_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_lt(v_i_1497_, v_sz_1496_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_dec_ref(v_getTokens_1494_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_b_1498_);
lean_ctor_set(v___x_1501_, 1, v___y_1499_);
return v___x_1501_;
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v_snd_1504_; lean_object* v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; 
v_a_1502_ = lean_array_uget_borrowed(v_as_1495_, v_i_1497_);
lean_inc(v_a_1502_);
lean_inc_ref(v_getTokens_1494_);
v___x_1503_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goOrderedItem(v_text_1493_, v_getTokens_1494_, v_a_1502_, v___y_1499_);
v_snd_1504_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_snd_1504_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = lean_box(0);
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1497_, v___x_1506_);
v_i_1497_ = v___x_1507_;
v_b_1498_ = v___x_1505_;
v___y_1499_ = v_snd_1504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(lean_object* v_text_1509_, lean_object* v_getTokens_1510_, lean_object* v_item_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_marker_1513_; lean_object* v_term_1514_; lean_object* v_desc_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v_snd_1518_; lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; lean_object* v_snd_1523_; size_t v_sz_1524_; lean_object* v___x_1525_; lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_marker_1513_ = lean_ctor_get(v_item_1511_, 1);
lean_inc(v_marker_1513_);
v_term_1514_ = lean_ctor_get(v_item_1511_, 2);
lean_inc_ref(v_term_1514_);
v_desc_1515_ = lean_ctor_get(v_item_1511_, 3);
lean_inc_ref(v_desc_1515_);
lean_dec_ref(v_item_1511_);
v___x_1516_ = 0;
v___x_1517_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1513_, v___x_1516_, v_a_1512_);
v_snd_1518_ = lean_ctor_get(v___x_1517_, 1);
lean_inc(v_snd_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = lean_box(0);
v_sz_1520_ = lean_array_size(v_term_1514_);
v___x_1521_ = ((size_t)0ULL);
lean_inc_ref(v_getTokens_1510_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1509_, v_getTokens_1510_, v_term_1514_, v_sz_1520_, v___x_1521_, v___x_1519_, v_snd_1518_);
lean_dec_ref(v_term_1514_);
v_snd_1523_ = lean_ctor_get(v___x_1522_, 1);
lean_inc(v_snd_1523_);
lean_dec_ref(v___x_1522_);
v_sz_1524_ = lean_array_size(v_desc_1515_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1509_, v_getTokens_1510_, v_desc_1515_, v_sz_1524_, v___x_1521_, v___x_1519_, v_snd_1523_);
lean_dec_ref(v_desc_1515_);
v_snd_1526_ = lean_ctor_get(v___x_1525_, 1);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1533_ == 0)
{
lean_object* v_unused_1534_; 
v_unused_1534_ = lean_ctor_get(v___x_1525_, 0);
lean_dec(v_unused_1534_);
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1519_);
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_snd_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(lean_object* v_text_1535_, lean_object* v_getTokens_1536_, lean_object* v_as_1537_, size_t v_sz_1538_, size_t v_i_1539_, lean_object* v_b_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_usize_dec_lt(v_i_1539_, v_sz_1538_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_dec_ref(v_getTokens_1536_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_b_1540_);
lean_ctor_set(v___x_1543_, 1, v___y_1541_);
return v___x_1543_;
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1545_; lean_object* v_snd_1546_; lean_object* v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; 
v_a_1544_ = lean_array_uget_borrowed(v_as_1537_, v_i_1539_);
lean_inc(v_a_1544_);
lean_inc_ref(v_getTokens_1536_);
v___x_1545_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(v_text_1535_, v_getTokens_1536_, v_a_1544_, v___y_1541_);
v_snd_1546_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_snd_1546_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = lean_box(0);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_add(v_i_1539_, v___x_1548_);
v_i_1539_ = v___x_1549_;
v_b_1540_ = v___x_1547_;
v___y_1541_ = v_snd_1546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_text_1567_, lean_object* v_getTokens_1568_, lean_object* v_stx_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1586_; 
lean_inc(v_stx_1569_);
v___x_1586_ = l_Lean_Doc_InlineView_of(v_stx_1569_);
if (lean_obj_tag(v___x_1586_) == 1)
{
lean_object* v_val_1587_; 
lean_dec(v_stx_1569_);
v_val_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v___x_1586_, 1);
switch(lean_obj_tag(v_val_1587_))
{
case 1:
{
lean_object* v_view_1588_; lean_object* v_opener_1589_; lean_object* v_content_1590_; lean_object* v_closer_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v_snd_1594_; lean_object* v___x_1595_; size_t v_sz_1596_; size_t v___x_1597_; lean_object* v___x_1598_; lean_object* v_snd_1599_; lean_object* v___x_1600_; 
v_view_1588_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_view_1588_);
lean_dec_ref_known(v_val_1587_, 1);
v_opener_1589_ = lean_ctor_get(v_view_1588_, 1);
lean_inc(v_opener_1589_);
v_content_1590_ = lean_ctor_get(v_view_1588_, 2);
lean_inc_ref(v_content_1590_);
v_closer_1591_ = lean_ctor_get(v_view_1588_, 3);
lean_inc(v_closer_1591_);
lean_dec_ref(v_view_1588_);
v___x_1592_ = 0;
v___x_1593_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1589_, v___x_1592_, v_a_1570_);
v_snd_1594_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_snd_1594_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = lean_box(0);
v_sz_1596_ = lean_array_size(v_content_1590_);
v___x_1597_ = ((size_t)0ULL);
v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1590_, v_sz_1596_, v___x_1597_, v___x_1595_, v_snd_1594_);
lean_dec_ref(v_content_1590_);
v_snd_1599_ = lean_ctor_get(v___x_1598_, 1);
lean_inc(v_snd_1599_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1591_, v___x_1592_, v_snd_1599_);
return v___x_1600_;
}
case 2:
{
lean_object* v_view_1601_; lean_object* v_opener_1602_; lean_object* v_content_1603_; lean_object* v_closer_1604_; uint8_t v___x_1605_; lean_object* v___x_1606_; lean_object* v_snd_1607_; lean_object* v___x_1608_; size_t v_sz_1609_; size_t v___x_1610_; lean_object* v___x_1611_; lean_object* v_snd_1612_; lean_object* v___x_1613_; 
v_view_1601_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_view_1601_);
lean_dec_ref_known(v_val_1587_, 1);
v_opener_1602_ = lean_ctor_get(v_view_1601_, 1);
lean_inc(v_opener_1602_);
v_content_1603_ = lean_ctor_get(v_view_1601_, 2);
lean_inc_ref(v_content_1603_);
v_closer_1604_ = lean_ctor_get(v_view_1601_, 3);
lean_inc(v_closer_1604_);
lean_dec_ref(v_view_1601_);
v___x_1605_ = 0;
v___x_1606_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1602_, v___x_1605_, v_a_1570_);
v_snd_1607_ = lean_ctor_get(v___x_1606_, 1);
lean_inc(v_snd_1607_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = lean_box(0);
v_sz_1609_ = lean_array_size(v_content_1603_);
v___x_1610_ = ((size_t)0ULL);
v___x_1611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1603_, v_sz_1609_, v___x_1610_, v___x_1608_, v_snd_1607_);
lean_dec_ref(v_content_1603_);
v_snd_1612_ = lean_ctor_get(v___x_1611_, 1);
lean_inc(v_snd_1612_);
lean_dec_ref(v___x_1611_);
v___x_1613_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1604_, v___x_1605_, v_snd_1612_);
return v___x_1613_;
}
case 3:
{
lean_object* v_view_1614_; lean_object* v___x_1615_; 
lean_dec_ref(v_getTokens_1568_);
v_view_1614_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_view_1614_);
lean_dec_ref_known(v_val_1587_, 1);
v___x_1615_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_view_1614_, v_a_1570_);
return v___x_1615_;
}
case 4:
{
lean_object* v_view_1616_; lean_object* v_marker_1617_; lean_object* v_code_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v_snd_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_getTokens_1568_);
v_view_1616_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_view_1616_);
lean_dec_ref_known(v_val_1587_, 1);
v_marker_1617_ = lean_ctor_get(v_view_1616_, 1);
lean_inc(v_marker_1617_);
v_code_1618_ = lean_ctor_get(v_view_1616_, 2);
lean_inc_ref(v_code_1618_);
lean_dec_ref(v_view_1616_);
v___x_1619_ = 0;
v___x_1620_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1617_, v___x_1619_, v_a_1570_);
v_snd_1621_ = lean_ctor_get(v___x_1620_, 1);
lean_inc(v_snd_1621_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_code_1618_, v_snd_1621_);
return v___x_1622_;
}
case 5:
{
lean_object* v_view_1623_; lean_object* v_opener_1624_; lean_object* v_content_1625_; lean_object* v_closer_1626_; lean_object* v_target_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v_snd_1630_; lean_object* v___x_1631_; size_t v_sz_1632_; size_t v___x_1633_; lean_object* v___x_1634_; lean_object* v_snd_1635_; lean_object* v___x_1636_; lean_object* v_snd_1637_; lean_object* v___x_1638_; 
v_view_1623_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_view_1623_);
lean_dec_ref_known(v_val_1587_, 1);
v_opener_1624_ = lean_ctor_get(v_view_1623_, 1);
lean_inc(v_opener_1624_);
v_content_1625_ = lean_ctor_get(v_view_1623_, 2);
lean_inc_ref(v_content_1625_);
v_closer_1626_ = lean_ctor_get(v_view_1623_, 3);
lean_inc(v_closer_1626_);
v_target_1627_ = lean_ctor_get(v_view_1623_, 4);
lean_inc_ref(v_target_1627_);
lean_dec_ref(v_view_1623_);
v___x_1628_ = 0;
v___x_1629_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1624_, v___x_1628_, v_a_1570_);
v_snd_1630_ = lean_ctor_get(v___x_1629_, 1);
lean_inc(v_snd_1630_);
lean_dec_ref(v___x_1629_);
v___x_1631_ = lean_box(0);
v_sz_1632_ = lean_array_size(v_content_1625_);
v___x_1633_ = ((size_t)0ULL);
v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1625_, v_sz_1632_, v___x_1633_, v___x_1631_, v_snd_1630_);
lean_dec_ref(v_content_1625_);
v_snd_1635_ = lean_ctor_get(v___x_1634_, 1);
lean_inc(v_snd_1635_);
lean_dec_ref(v___x_1634_);
v___x_1636_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1626_, v___x_1628_, v_snd_1635_);
v_snd_1637_ = lean_ctor_get(v___x_1636_, 1);
lean_inc(v_snd_1637_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1627_, v_snd_1637_);
return v___x_1638_;
}
case 6:
{
lean_object* v_view_1639_; lean_object* v_opener_1640_; lean_object* v_alt_1641_; lean_object* v_closer_1642_; lean_object* v_target_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v_snd_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v_snd_1649_; lean_object* v___x_1650_; lean_object* v_snd_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v_getTokens_1568_);
v_view_1639_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_view_1639_);
lean_dec_ref_known(v_val_1587_, 1);
v_opener_1640_ = lean_ctor_get(v_view_1639_, 1);
lean_inc(v_opener_1640_);
v_alt_1641_ = lean_ctor_get(v_view_1639_, 2);
lean_inc(v_alt_1641_);
v_closer_1642_ = lean_ctor_get(v_view_1639_, 3);
lean_inc(v_closer_1642_);
v_target_1643_ = lean_ctor_get(v_view_1639_, 4);
lean_inc_ref(v_target_1643_);
lean_dec_ref(v_view_1639_);
v___x_1644_ = 0;
v___x_1645_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1640_, v___x_1644_, v_a_1570_);
v_snd_1646_ = lean_ctor_get(v___x_1645_, 1);
lean_inc(v_snd_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = 18;
v___x_1648_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_alt_1641_, v___x_1647_, v_snd_1646_);
v_snd_1649_ = lean_ctor_get(v___x_1648_, 1);
lean_inc(v_snd_1649_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1642_, v___x_1644_, v_snd_1649_);
v_snd_1651_ = lean_ctor_get(v___x_1650_, 1);
lean_inc(v_snd_1651_);
lean_dec_ref(v___x_1650_);
v___x_1652_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1643_, v_snd_1651_);
return v___x_1652_;
}
case 7:
{
lean_object* v_view_1653_; lean_object* v_opener_1654_; lean_object* v_name_1655_; lean_object* v_closer_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v_snd_1659_; uint8_t v___x_1660_; lean_object* v___x_1661_; lean_object* v_snd_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v_getTokens_1568_);
v_view_1653_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_view_1653_);
lean_dec_ref_known(v_val_1587_, 1);
v_opener_1654_ = lean_ctor_get(v_view_1653_, 1);
lean_inc(v_opener_1654_);
v_name_1655_ = lean_ctor_get(v_view_1653_, 2);
lean_inc(v_name_1655_);
v_closer_1656_ = lean_ctor_get(v_view_1653_, 3);
lean_inc(v_closer_1656_);
lean_dec_ref(v_view_1653_);
v___x_1657_ = 0;
v___x_1658_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1654_, v___x_1657_, v_a_1570_);
v_snd_1659_ = lean_ctor_get(v___x_1658_, 1);
lean_inc(v_snd_1659_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = 2;
v___x_1661_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1655_, v___x_1660_, v_snd_1659_);
v_snd_1662_ = lean_ctor_get(v___x_1661_, 1);
lean_inc(v_snd_1662_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1656_, v___x_1657_, v_snd_1662_);
return v___x_1663_;
}
case 9:
{
lean_object* v_view_1664_; lean_object* v_braceOpen_1665_; lean_object* v_name_1666_; lean_object* v_args_1667_; lean_object* v_braceClose_1668_; lean_object* v_brackets_1669_; lean_object* v_content_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v_snd_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; lean_object* v_snd_1676_; lean_object* v___x_1677_; lean_object* v___y_1679_; size_t v_sz_1696_; size_t v___x_1697_; lean_object* v___x_1698_; lean_object* v_snd_1699_; lean_object* v___x_1700_; 
v_view_1664_ = lean_ctor_get(v_val_1587_, 0);
lean_inc_ref(v_view_1664_);
lean_dec_ref_known(v_val_1587_, 1);
v_braceOpen_1665_ = lean_ctor_get(v_view_1664_, 1);
lean_inc(v_braceOpen_1665_);
v_name_1666_ = lean_ctor_get(v_view_1664_, 2);
lean_inc(v_name_1666_);
v_args_1667_ = lean_ctor_get(v_view_1664_, 3);
lean_inc_ref(v_args_1667_);
v_braceClose_1668_ = lean_ctor_get(v_view_1664_, 4);
lean_inc(v_braceClose_1668_);
v_brackets_1669_ = lean_ctor_get(v_view_1664_, 5);
lean_inc(v_brackets_1669_);
v_content_1670_ = lean_ctor_get(v_view_1664_, 6);
lean_inc_ref(v_content_1670_);
lean_dec_ref(v_view_1664_);
v___x_1671_ = 0;
v___x_1672_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1665_, v___x_1671_, v_a_1570_);
v_snd_1673_ = lean_ctor_get(v___x_1672_, 1);
lean_inc(v_snd_1673_);
lean_dec_ref(v___x_1672_);
v___x_1674_ = 3;
v___x_1675_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1666_, v___x_1674_, v_snd_1673_);
v_snd_1676_ = lean_ctor_get(v___x_1675_, 1);
lean_inc(v_snd_1676_);
lean_dec_ref(v___x_1675_);
v___x_1677_ = lean_box(0);
v_sz_1696_ = lean_array_size(v_args_1667_);
v___x_1697_ = ((size_t)0ULL);
v___x_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_args_1667_, v_sz_1696_, v___x_1697_, v___x_1677_, v_snd_1676_);
lean_dec_ref(v_args_1667_);
v_snd_1699_ = lean_ctor_get(v___x_1698_, 1);
lean_inc(v_snd_1699_);
lean_dec_ref(v___x_1698_);
v___x_1700_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1668_, v___x_1671_, v_snd_1699_);
if (lean_obj_tag(v_brackets_1669_) == 1)
{
lean_object* v_val_1701_; lean_object* v_snd_1702_; lean_object* v_fst_1703_; lean_object* v___x_1704_; lean_object* v_snd_1705_; 
v_val_1701_ = lean_ctor_get(v_brackets_1669_, 0);
v_snd_1702_ = lean_ctor_get(v___x_1700_, 1);
lean_inc(v_snd_1702_);
lean_dec_ref(v___x_1700_);
v_fst_1703_ = lean_ctor_get(v_val_1701_, 0);
lean_inc(v_fst_1703_);
v___x_1704_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1703_, v___x_1671_, v_snd_1702_);
v_snd_1705_ = lean_ctor_get(v___x_1704_, 1);
lean_inc(v_snd_1705_);
lean_dec_ref(v___x_1704_);
v___y_1679_ = v_snd_1705_;
goto v___jp_1678_;
}
else
{
lean_object* v_snd_1706_; 
v_snd_1706_ = lean_ctor_get(v___x_1700_, 1);
lean_inc(v_snd_1706_);
lean_dec_ref(v___x_1700_);
v___y_1679_ = v_snd_1706_;
goto v___jp_1678_;
}
v___jp_1678_:
{
size_t v_sz_1680_; size_t v___x_1681_; lean_object* v___x_1682_; 
v_sz_1680_ = lean_array_size(v_content_1670_);
v___x_1681_ = ((size_t)0ULL);
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1670_, v_sz_1680_, v___x_1681_, v___x_1677_, v___y_1679_);
lean_dec_ref(v_content_1670_);
if (lean_obj_tag(v_brackets_1669_) == 1)
{
lean_object* v_val_1683_; lean_object* v_snd_1684_; lean_object* v_snd_1685_; lean_object* v___x_1686_; 
v_val_1683_ = lean_ctor_get(v_brackets_1669_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v_brackets_1669_, 1);
v_snd_1684_ = lean_ctor_get(v___x_1682_, 1);
lean_inc(v_snd_1684_);
lean_dec_ref(v___x_1682_);
v_snd_1685_ = lean_ctor_get(v_val_1683_, 1);
lean_inc(v_snd_1685_);
lean_dec(v_val_1683_);
v___x_1686_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1685_, v___x_1671_, v_snd_1684_);
return v___x_1686_;
}
else
{
lean_object* v_snd_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_brackets_1669_);
v_snd_1687_ = lean_ctor_get(v___x_1682_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v___x_1682_, 0);
lean_dec(v_unused_1695_);
v___x_1689_ = v___x_1682_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_snd_1687_);
lean_dec(v___x_1682_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1677_);
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_snd_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
default: 
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec(v_val_1587_);
lean_dec_ref(v_getTokens_1568_);
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v_a_1570_);
return v___x_1708_;
}
}
}
else
{
lean_object* v___x_1709_; 
lean_dec(v___x_1586_);
lean_inc(v_stx_1569_);
v___x_1709_ = l_Lean_Doc_BlockView_of(v_stx_1569_);
if (lean_obj_tag(v___x_1709_) == 1)
{
lean_object* v_val_1710_; 
lean_dec(v_stx_1569_);
v_val_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v___x_1709_, 1);
switch(lean_obj_tag(v_val_1710_))
{
case 0:
{
lean_object* v_view_1711_; lean_object* v_content_1712_; lean_object* v___x_1713_; size_t v_sz_1714_; size_t v___x_1715_; lean_object* v___x_1716_; lean_object* v_snd_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_view_1711_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1711_);
lean_dec_ref_known(v_val_1710_, 1);
v_content_1712_ = lean_ctor_get(v_view_1711_, 1);
lean_inc_ref(v_content_1712_);
lean_dec_ref(v_view_1711_);
v___x_1713_ = lean_box(0);
v_sz_1714_ = lean_array_size(v_content_1712_);
v___x_1715_ = ((size_t)0ULL);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1712_, v_sz_1714_, v___x_1715_, v___x_1713_, v_a_1570_);
lean_dec_ref(v_content_1712_);
v_snd_1717_ = lean_ctor_get(v___x_1716_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v___x_1716_, 0);
lean_dec(v_unused_1725_);
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snd_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1713_);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_snd_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
case 1:
{
lean_object* v_view_1726_; lean_object* v_items_1727_; lean_object* v___x_1728_; size_t v_sz_1729_; size_t v___x_1730_; lean_object* v___x_1731_; lean_object* v_snd_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_view_1726_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1726_);
lean_dec_ref_known(v_val_1710_, 1);
v_items_1727_ = lean_ctor_get(v_view_1726_, 1);
lean_inc_ref(v_items_1727_);
lean_dec_ref(v_view_1726_);
v___x_1728_ = lean_box(0);
v_sz_1729_ = lean_array_size(v_items_1727_);
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_text_1567_, v_getTokens_1568_, v_items_1727_, v_sz_1729_, v___x_1730_, v___x_1728_, v_a_1570_);
lean_dec_ref(v_items_1727_);
v_snd_1732_ = lean_ctor_get(v___x_1731_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v___x_1731_, 0);
lean_dec(v_unused_1740_);
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snd_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1728_);
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_snd_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
case 2:
{
lean_object* v_view_1741_; lean_object* v_items_1742_; lean_object* v___x_1743_; size_t v_sz_1744_; size_t v___x_1745_; lean_object* v___x_1746_; lean_object* v_snd_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_view_1741_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1741_);
lean_dec_ref_known(v_val_1710_, 1);
v_items_1742_ = lean_ctor_get(v_view_1741_, 2);
lean_inc_ref(v_items_1742_);
lean_dec_ref(v_view_1741_);
v___x_1743_ = lean_box(0);
v_sz_1744_ = lean_array_size(v_items_1742_);
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_text_1567_, v_getTokens_1568_, v_items_1742_, v_sz_1744_, v___x_1745_, v___x_1743_, v_a_1570_);
lean_dec_ref(v_items_1742_);
v_snd_1747_ = lean_ctor_get(v___x_1746_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1746_, 0);
lean_dec(v_unused_1755_);
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_snd_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1743_);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_snd_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
case 3:
{
lean_object* v_view_1756_; lean_object* v_items_1757_; lean_object* v___x_1758_; size_t v_sz_1759_; size_t v___x_1760_; lean_object* v___x_1761_; lean_object* v_snd_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_view_1756_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1756_);
lean_dec_ref_known(v_val_1710_, 1);
v_items_1757_ = lean_ctor_get(v_view_1756_, 1);
lean_inc_ref(v_items_1757_);
lean_dec_ref(v_view_1756_);
v___x_1758_ = lean_box(0);
v_sz_1759_ = lean_array_size(v_items_1757_);
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_text_1567_, v_getTokens_1568_, v_items_1757_, v_sz_1759_, v___x_1760_, v___x_1758_, v_a_1570_);
lean_dec_ref(v_items_1757_);
v_snd_1762_ = lean_ctor_get(v___x_1761_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1761_, 0);
lean_dec(v_unused_1770_);
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_snd_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1758_);
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_snd_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
case 4:
{
lean_object* v_view_1771_; lean_object* v_marker_1772_; lean_object* v_content_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v_snd_1776_; lean_object* v___x_1777_; size_t v_sz_1778_; size_t v___x_1779_; lean_object* v___x_1780_; lean_object* v_snd_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_view_1771_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1771_);
lean_dec_ref_known(v_val_1710_, 1);
v_marker_1772_ = lean_ctor_get(v_view_1771_, 1);
lean_inc(v_marker_1772_);
v_content_1773_ = lean_ctor_get(v_view_1771_, 2);
lean_inc_ref(v_content_1773_);
lean_dec_ref(v_view_1771_);
v___x_1774_ = 0;
v___x_1775_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1772_, v___x_1774_, v_a_1570_);
v_snd_1776_ = lean_ctor_get(v___x_1775_, 1);
lean_inc(v_snd_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = lean_box(0);
v_sz_1778_ = lean_array_size(v_content_1773_);
v___x_1779_ = ((size_t)0ULL);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1773_, v_sz_1778_, v___x_1779_, v___x_1777_, v_snd_1776_);
lean_dec_ref(v_content_1773_);
v_snd_1781_ = lean_ctor_get(v___x_1780_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v___x_1780_, 0);
lean_dec(v_unused_1789_);
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_snd_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1777_);
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_snd_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
case 5:
{
lean_object* v_view_1790_; lean_object* v_openFence_1791_; lean_object* v_name_x3f_1792_; lean_object* v_args_1793_; lean_object* v_content_1794_; lean_object* v_closeFence_1795_; uint8_t v___x_1796_; lean_object* v___y_1798_; lean_object* v___x_1806_; 
lean_dec_ref(v_getTokens_1568_);
v_view_1790_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1790_);
lean_dec_ref_known(v_val_1710_, 1);
v_openFence_1791_ = lean_ctor_get(v_view_1790_, 1);
lean_inc(v_openFence_1791_);
v_name_x3f_1792_ = lean_ctor_get(v_view_1790_, 2);
lean_inc(v_name_x3f_1792_);
v_args_1793_ = lean_ctor_get(v_view_1790_, 3);
lean_inc_ref(v_args_1793_);
v_content_1794_ = lean_ctor_get(v_view_1790_, 4);
lean_inc(v_content_1794_);
v_closeFence_1795_ = lean_ctor_get(v_view_1790_, 5);
lean_inc(v_closeFence_1795_);
lean_dec_ref(v_view_1790_);
v___x_1796_ = 0;
v___x_1806_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_openFence_1791_, v___x_1796_, v_a_1570_);
if (lean_obj_tag(v_name_x3f_1792_) == 1)
{
lean_object* v_snd_1807_; lean_object* v_val_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v_snd_1811_; lean_object* v___x_1812_; size_t v_sz_1813_; size_t v___x_1814_; lean_object* v___x_1815_; lean_object* v_snd_1816_; 
v_snd_1807_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_snd_1807_);
lean_dec_ref(v___x_1806_);
v_val_1808_ = lean_ctor_get(v_name_x3f_1792_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v_name_x3f_1792_, 1);
v___x_1809_ = 3;
v___x_1810_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1808_, v___x_1809_, v_snd_1807_);
v_snd_1811_ = lean_ctor_get(v___x_1810_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = lean_box(0);
v_sz_1813_ = lean_array_size(v_args_1793_);
v___x_1814_ = ((size_t)0ULL);
v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_args_1793_, v_sz_1813_, v___x_1814_, v___x_1812_, v_snd_1811_);
lean_dec_ref(v_args_1793_);
v_snd_1816_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_snd_1816_);
lean_dec_ref(v___x_1815_);
v___y_1798_ = v_snd_1816_;
goto v___jp_1797_;
}
else
{
lean_object* v_snd_1817_; 
lean_dec_ref(v_args_1793_);
lean_dec(v_name_x3f_1792_);
v_snd_1817_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_snd_1817_);
lean_dec_ref(v___x_1806_);
v___y_1798_ = v_snd_1817_;
goto v___jp_1797_;
}
v___jp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; lean_object* v_snd_1804_; lean_object* v___x_1805_; 
v___x_1799_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_content_1794_);
lean_dec(v_content_1794_);
v___x_1800_ = lean_box(0);
v_sz_1801_ = lean_array_size(v___x_1799_);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__7(v_text_1567_, v___x_1799_, v_sz_1801_, v___x_1802_, v___x_1800_, v___y_1798_);
lean_dec_ref(v___x_1799_);
v_snd_1804_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_snd_1804_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closeFence_1795_, v___x_1796_, v_snd_1804_);
return v___x_1805_;
}
}
case 6:
{
lean_object* v_view_1818_; lean_object* v_opener_1819_; lean_object* v_name_1820_; lean_object* v_args_1821_; lean_object* v_content_1822_; lean_object* v_closer_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v_snd_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v_snd_1829_; lean_object* v___x_1830_; size_t v_sz_1831_; size_t v___x_1832_; lean_object* v___x_1833_; lean_object* v_snd_1834_; size_t v_sz_1835_; lean_object* v___x_1836_; lean_object* v_snd_1837_; lean_object* v___x_1838_; 
v_view_1818_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1818_);
lean_dec_ref_known(v_val_1710_, 1);
v_opener_1819_ = lean_ctor_get(v_view_1818_, 1);
lean_inc(v_opener_1819_);
v_name_1820_ = lean_ctor_get(v_view_1818_, 2);
lean_inc(v_name_1820_);
v_args_1821_ = lean_ctor_get(v_view_1818_, 3);
lean_inc_ref(v_args_1821_);
v_content_1822_ = lean_ctor_get(v_view_1818_, 4);
lean_inc_ref(v_content_1822_);
v_closer_1823_ = lean_ctor_get(v_view_1818_, 5);
lean_inc(v_closer_1823_);
lean_dec_ref(v_view_1818_);
v___x_1824_ = 0;
v___x_1825_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1819_, v___x_1824_, v_a_1570_);
v_snd_1826_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_snd_1826_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = 3;
v___x_1828_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1820_, v___x_1827_, v_snd_1826_);
v_snd_1829_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_snd_1829_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = lean_box(0);
v_sz_1831_ = lean_array_size(v_args_1821_);
v___x_1832_ = ((size_t)0ULL);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_args_1821_, v_sz_1831_, v___x_1832_, v___x_1830_, v_snd_1829_);
lean_dec_ref(v_args_1821_);
v_snd_1834_ = lean_ctor_get(v___x_1833_, 1);
lean_inc(v_snd_1834_);
lean_dec_ref(v___x_1833_);
v_sz_1835_ = lean_array_size(v_content_1822_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1822_, v_sz_1835_, v___x_1832_, v___x_1830_, v_snd_1834_);
lean_dec_ref(v_content_1822_);
v_snd_1837_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_snd_1837_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1823_, v___x_1824_, v_snd_1837_);
return v___x_1838_;
}
case 7:
{
lean_object* v_view_1839_; lean_object* v_braceOpen_1840_; lean_object* v_name_1841_; lean_object* v_args_1842_; lean_object* v_braceClose_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v_snd_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v_snd_1849_; lean_object* v___x_1850_; size_t v_sz_1851_; size_t v___x_1852_; lean_object* v___x_1853_; lean_object* v_snd_1854_; lean_object* v___x_1855_; 
lean_dec_ref(v_getTokens_1568_);
v_view_1839_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1839_);
lean_dec_ref_known(v_val_1710_, 1);
v_braceOpen_1840_ = lean_ctor_get(v_view_1839_, 1);
lean_inc(v_braceOpen_1840_);
v_name_1841_ = lean_ctor_get(v_view_1839_, 2);
lean_inc(v_name_1841_);
v_args_1842_ = lean_ctor_get(v_view_1839_, 3);
lean_inc_ref(v_args_1842_);
v_braceClose_1843_ = lean_ctor_get(v_view_1839_, 4);
lean_inc(v_braceClose_1843_);
lean_dec_ref(v_view_1839_);
v___x_1844_ = 0;
v___x_1845_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1840_, v___x_1844_, v_a_1570_);
v_snd_1846_ = lean_ctor_get(v___x_1845_, 1);
lean_inc(v_snd_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = 3;
v___x_1848_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1841_, v___x_1847_, v_snd_1846_);
v_snd_1849_ = lean_ctor_get(v___x_1848_, 1);
lean_inc(v_snd_1849_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = lean_box(0);
v_sz_1851_ = lean_array_size(v_args_1842_);
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_args_1842_, v_sz_1851_, v___x_1852_, v___x_1850_, v_snd_1849_);
lean_dec_ref(v_args_1842_);
v_snd_1854_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_snd_1854_);
lean_dec_ref(v___x_1853_);
v___x_1855_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1843_, v___x_1844_, v_snd_1854_);
return v___x_1855_;
}
case 8:
{
lean_object* v_view_1856_; lean_object* v_marker_1857_; lean_object* v_content_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_1865_; lean_object* v_snd_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_view_1856_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1856_);
lean_dec_ref_known(v_val_1710_, 1);
v_marker_1857_ = lean_ctor_get(v_view_1856_, 1);
lean_inc(v_marker_1857_);
v_content_1858_ = lean_ctor_get(v_view_1856_, 3);
lean_inc_ref(v_content_1858_);
lean_dec_ref(v_view_1856_);
v___x_1859_ = 0;
v___x_1860_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1857_, v___x_1859_, v_a_1570_);
v_snd_1861_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_snd_1861_);
lean_dec_ref(v___x_1860_);
v___x_1862_ = lean_box(0);
v_sz_1863_ = lean_array_size(v_content_1858_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1858_, v_sz_1863_, v___x_1864_, v___x_1862_, v_snd_1861_);
lean_dec_ref(v_content_1858_);
v_snd_1866_ = lean_ctor_get(v___x_1865_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v___x_1865_, 0);
lean_dec(v_unused_1874_);
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_snd_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1862_);
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_snd_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
case 9:
{
lean_object* v_view_1875_; lean_object* v_opener_1876_; lean_object* v_name_1877_; lean_object* v_closer_1878_; lean_object* v_url_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v_snd_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v_snd_1885_; lean_object* v___x_1886_; lean_object* v_snd_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v_getTokens_1568_);
v_view_1875_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1875_);
lean_dec_ref_known(v_val_1710_, 1);
v_opener_1876_ = lean_ctor_get(v_view_1875_, 1);
lean_inc(v_opener_1876_);
v_name_1877_ = lean_ctor_get(v_view_1875_, 2);
lean_inc(v_name_1877_);
v_closer_1878_ = lean_ctor_get(v_view_1875_, 3);
lean_inc(v_closer_1878_);
v_url_1879_ = lean_ctor_get(v_view_1875_, 4);
lean_inc(v_url_1879_);
lean_dec_ref(v_view_1875_);
v___x_1880_ = 0;
v___x_1881_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1876_, v___x_1880_, v_a_1570_);
v_snd_1882_ = lean_ctor_get(v___x_1881_, 1);
lean_inc(v_snd_1882_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = 2;
v___x_1884_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1877_, v___x_1883_, v_snd_1882_);
v_snd_1885_ = lean_ctor_get(v___x_1884_, 1);
lean_inc(v_snd_1885_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1878_, v___x_1880_, v_snd_1885_);
v_snd_1887_ = lean_ctor_get(v___x_1886_, 1);
lean_inc(v_snd_1887_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = 18;
v___x_1889_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1879_, v___x_1888_, v_snd_1887_);
return v___x_1889_;
}
case 10:
{
lean_object* v_view_1890_; lean_object* v_opener_1891_; lean_object* v_name_1892_; lean_object* v_closer_1893_; lean_object* v_content_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v_snd_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; lean_object* v_snd_1900_; lean_object* v___x_1901_; lean_object* v_snd_1902_; lean_object* v___x_1903_; size_t v_sz_1904_; size_t v___x_1905_; lean_object* v___x_1906_; lean_object* v_snd_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_view_1890_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1890_);
lean_dec_ref_known(v_val_1710_, 1);
v_opener_1891_ = lean_ctor_get(v_view_1890_, 1);
lean_inc(v_opener_1891_);
v_name_1892_ = lean_ctor_get(v_view_1890_, 2);
lean_inc(v_name_1892_);
v_closer_1893_ = lean_ctor_get(v_view_1890_, 3);
lean_inc(v_closer_1893_);
v_content_1894_ = lean_ctor_get(v_view_1890_, 4);
lean_inc_ref(v_content_1894_);
lean_dec_ref(v_view_1890_);
v___x_1895_ = 0;
v___x_1896_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1891_, v___x_1895_, v_a_1570_);
v_snd_1897_ = lean_ctor_get(v___x_1896_, 1);
lean_inc(v_snd_1897_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = 2;
v___x_1899_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1892_, v___x_1898_, v_snd_1897_);
v_snd_1900_ = lean_ctor_get(v___x_1899_, 1);
lean_inc(v_snd_1900_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1893_, v___x_1895_, v_snd_1900_);
v_snd_1902_ = lean_ctor_get(v___x_1901_, 1);
lean_inc(v_snd_1902_);
lean_dec_ref(v___x_1901_);
v___x_1903_ = lean_box(0);
v_sz_1904_ = lean_array_size(v_content_1894_);
v___x_1905_ = ((size_t)0ULL);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1567_, v_getTokens_1568_, v_content_1894_, v_sz_1904_, v___x_1905_, v___x_1903_, v_snd_1902_);
lean_dec_ref(v_content_1894_);
v_snd_1907_ = lean_ctor_get(v___x_1906_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v___x_1906_, 0);
lean_dec(v_unused_1915_);
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_snd_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1903_);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_snd_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
default: 
{
lean_object* v_view_1916_; lean_object* v_opener_1917_; lean_object* v_contents_1918_; lean_object* v_closer_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v_snd_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_view_1916_ = lean_ctor_get(v_val_1710_, 0);
lean_inc_ref(v_view_1916_);
lean_dec_ref_known(v_val_1710_, 1);
v_opener_1917_ = lean_ctor_get(v_view_1916_, 1);
lean_inc(v_opener_1917_);
v_contents_1918_ = lean_ctor_get(v_view_1916_, 2);
lean_inc(v_contents_1918_);
v_closer_1919_ = lean_ctor_get(v_view_1916_, 3);
lean_inc(v_closer_1919_);
lean_dec_ref(v_view_1916_);
v___x_1920_ = 0;
v___x_1921_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1917_, v___x_1920_, v_a_1570_);
v_snd_1922_ = lean_ctor_get(v___x_1921_, 1);
lean_inc(v_snd_1922_);
lean_dec_ref(v___x_1921_);
v___x_1923_ = lean_apply_1(v_getTokens_1568_, v_contents_1918_);
v___x_1924_ = l_Array_append___redArg(v_snd_1922_, v___x_1923_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1919_, v___x_1920_, v___x_1924_);
return v___x_1925_;
}
}
}
else
{
lean_object* v_k_1926_; uint8_t v___y_1928_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
lean_dec(v___x_1709_);
lean_inc(v_stx_1569_);
v_k_1926_ = l_Lean_Syntax_getKind(v_stx_1569_);
v___x_1933_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3));
v___x_1934_ = lean_name_eq(v_k_1926_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6));
v___x_1936_ = lean_name_eq(v_k_1926_, v___x_1935_);
v___y_1928_ = v___x_1936_;
goto v___jp_1927_;
}
else
{
v___y_1928_ = v___x_1934_;
goto v___jp_1927_;
}
v___jp_1927_:
{
if (v___y_1928_ == 0)
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1));
v___x_1930_ = lean_name_eq(v_k_1926_, v___x_1929_);
lean_dec(v_k_1926_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec(v_stx_1569_);
lean_dec_ref(v_getTokens_1568_);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v_a_1570_);
return v___x_1932_;
}
else
{
goto v___jp_1571_;
}
}
else
{
lean_dec(v_k_1926_);
goto v___jp_1571_;
}
}
}
}
v___jp_1571_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1572_ = l_Lean_Syntax_getArgs(v_stx_1569_);
lean_dec(v_stx_1569_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_array_get_size(v___x_1572_);
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_nat_dec_lt(v___x_1573_, v___x_1574_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_getTokens_1568_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v_a_1570_);
return v___x_1577_;
}
else
{
uint8_t v___x_1578_; 
v___x_1578_ = lean_nat_dec_le(v___x_1574_, v___x_1574_);
if (v___x_1578_ == 0)
{
if (v___x_1576_ == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_getTokens_1568_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1575_);
lean_ctor_set(v___x_1579_, 1, v_a_1570_);
return v___x_1579_;
}
else
{
size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = lean_usize_of_nat(v___x_1574_);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_text_1567_, v_getTokens_1568_, v___x_1572_, v___x_1580_, v___x_1581_, v___x_1575_, v_a_1570_);
lean_dec_ref(v___x_1572_);
return v___x_1582_;
}
}
else
{
size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = lean_usize_of_nat(v___x_1574_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_text_1567_, v_getTokens_1568_, v___x_1572_, v___x_1583_, v___x_1584_, v___x_1575_, v_a_1570_);
lean_dec_ref(v___x_1572_);
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(lean_object* v_text_1937_, lean_object* v_getTokens_1938_, lean_object* v_as_1939_, size_t v_i_1940_, size_t v_stop_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_){
_start:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_usize_dec_eq(v_i_1940_, v_stop_1941_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_fst_1947_; lean_object* v_snd_1948_; size_t v___x_1949_; size_t v___x_1950_; 
v___x_1945_ = lean_array_uget_borrowed(v_as_1939_, v_i_1940_);
lean_inc(v___x_1945_);
lean_inc_ref(v_getTokens_1938_);
v___x_1946_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1937_, v_getTokens_1938_, v___x_1945_, v___y_1943_);
v_fst_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_fst_1947_);
v_snd_1948_ = lean_ctor_get(v___x_1946_, 1);
lean_inc(v_snd_1948_);
lean_dec_ref(v___x_1946_);
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_add(v_i_1940_, v___x_1949_);
v_i_1940_ = v___x_1950_;
v_b_1942_ = v_fst_1947_;
v___y_1943_ = v_snd_1948_;
goto _start;
}
else
{
lean_object* v___x_1952_; 
lean_dec_ref(v_getTokens_1938_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_b_1942_);
lean_ctor_set(v___x_1952_, 1, v___y_1943_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2___boxed(lean_object* v_text_1953_, lean_object* v_getTokens_1954_, lean_object* v_as_1955_, lean_object* v_i_1956_, lean_object* v_stop_1957_, lean_object* v_b_1958_, lean_object* v___y_1959_){
_start:
{
size_t v_i_boxed_1960_; size_t v_stop_boxed_1961_; lean_object* v_res_1962_; 
v_i_boxed_1960_ = lean_unbox_usize(v_i_1956_);
lean_dec(v_i_1956_);
v_stop_boxed_1961_ = lean_unbox_usize(v_stop_1957_);
lean_dec(v_stop_1957_);
v_res_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_text_1953_, v_getTokens_1954_, v_as_1955_, v_i_boxed_1960_, v_stop_boxed_1961_, v_b_1958_, v___y_1959_);
lean_dec_ref(v_as_1955_);
lean_dec_ref(v_text_1953_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4___boxed(lean_object* v_text_1963_, lean_object* v_getTokens_1964_, lean_object* v_as_1965_, lean_object* v_sz_1966_, lean_object* v_i_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_){
_start:
{
size_t v_sz_boxed_1970_; size_t v_i_boxed_1971_; lean_object* v_res_1972_; 
v_sz_boxed_1970_ = lean_unbox_usize(v_sz_1966_);
lean_dec(v_sz_1966_);
v_i_boxed_1971_ = lean_unbox_usize(v_i_1967_);
lean_dec(v_i_1967_);
v_res_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_text_1963_, v_getTokens_1964_, v_as_1965_, v_sz_boxed_1970_, v_i_boxed_1971_, v_b_1968_, v___y_1969_);
lean_dec_ref(v_as_1965_);
lean_dec_ref(v_text_1963_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5___boxed(lean_object* v_text_1973_, lean_object* v_getTokens_1974_, lean_object* v_as_1975_, lean_object* v_sz_1976_, lean_object* v_i_1977_, lean_object* v_b_1978_, lean_object* v___y_1979_){
_start:
{
size_t v_sz_boxed_1980_; size_t v_i_boxed_1981_; lean_object* v_res_1982_; 
v_sz_boxed_1980_ = lean_unbox_usize(v_sz_1976_);
lean_dec(v_sz_1976_);
v_i_boxed_1981_ = lean_unbox_usize(v_i_1977_);
lean_dec(v_i_1977_);
v_res_1982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_text_1973_, v_getTokens_1974_, v_as_1975_, v_sz_boxed_1980_, v_i_boxed_1981_, v_b_1978_, v___y_1979_);
lean_dec_ref(v_as_1975_);
lean_dec_ref(v_text_1973_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6___boxed(lean_object* v_text_1983_, lean_object* v_getTokens_1984_, lean_object* v_as_1985_, lean_object* v_sz_1986_, lean_object* v_i_1987_, lean_object* v_b_1988_, lean_object* v___y_1989_){
_start:
{
size_t v_sz_boxed_1990_; size_t v_i_boxed_1991_; lean_object* v_res_1992_; 
v_sz_boxed_1990_ = lean_unbox_usize(v_sz_1986_);
lean_dec(v_sz_1986_);
v_i_boxed_1991_ = lean_unbox_usize(v_i_1987_);
lean_dec(v_i_1987_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_text_1983_, v_getTokens_1984_, v_as_1985_, v_sz_boxed_1990_, v_i_boxed_1991_, v_b_1988_, v___y_1989_);
lean_dec_ref(v_as_1985_);
lean_dec_ref(v_text_1983_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0___boxed(lean_object* v_text_1993_, lean_object* v_getTokens_1994_, lean_object* v_as_1995_, lean_object* v_sz_1996_, lean_object* v_i_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_){
_start:
{
size_t v_sz_boxed_2000_; size_t v_i_boxed_2001_; lean_object* v_res_2002_; 
v_sz_boxed_2000_ = lean_unbox_usize(v_sz_1996_);
lean_dec(v_sz_1996_);
v_i_boxed_2001_ = lean_unbox_usize(v_i_1997_);
lean_dec(v_i_1997_);
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem_spec__0(v_text_1993_, v_getTokens_1994_, v_as_1995_, v_sz_boxed_2000_, v_i_boxed_2001_, v_b_1998_, v___y_1999_);
lean_dec_ref(v_as_1995_);
lean_dec_ref(v_text_1993_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goOrderedItem___boxed(lean_object* v_text_2003_, lean_object* v_getTokens_2004_, lean_object* v_item_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goOrderedItem(v_text_2003_, v_getTokens_2004_, v_item_2005_, v_a_2006_);
lean_dec_ref(v_text_2003_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem___boxed(lean_object* v_text_2008_, lean_object* v_getTokens_2009_, lean_object* v_item_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goUnorderedItem(v_text_2008_, v_getTokens_2009_, v_item_2010_, v_a_2011_);
lean_dec_ref(v_text_2008_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc___boxed(lean_object* v_text_2013_, lean_object* v_getTokens_2014_, lean_object* v_item_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(v_text_2013_, v_getTokens_2014_, v_item_2015_, v_a_2016_);
lean_dec_ref(v_text_2013_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___boxed(lean_object* v_text_2018_, lean_object* v_getTokens_2019_, lean_object* v_stx_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2018_, v_getTokens_2019_, v_stx_2020_, v_a_2021_);
lean_dec_ref(v_text_2018_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_text_2025_, lean_object* v_stx_2026_, lean_object* v_getTokens_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v_snd_2030_; 
v___x_2028_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_2029_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2025_, v_getTokens_2027_, v_stx_2026_, v___x_2028_);
v_snd_2030_ = lean_ctor_get(v___x_2029_, 1);
lean_inc(v_snd_2030_);
lean_dec_ref(v___x_2029_);
return v_snd_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___boxed(lean_object* v_text_2031_, lean_object* v_stx_2032_, lean_object* v_getTokens_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2031_, v_stx_2032_, v_getTokens_2033_);
lean_dec_ref(v_text_2031_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_2035_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v_decide_2038_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = lean_string_utf8_byte_size(v_s_2035_);
v_decide_2038_ = lean_nat_dec_eq(v___x_2036_, v___x_2037_);
if (v_decide_2038_ == 0)
{
uint32_t v___x_2039_; uint32_t v___x_2040_; uint8_t v___x_2041_; 
v___x_2039_ = 35;
v___x_2040_ = lean_string_utf8_get_fast(v_s_2035_, v___x_2036_);
v___x_2041_ = lean_uint32_dec_eq(v___x_2040_, v___x_2039_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_dec_ref(v_s_2035_);
v___x_2042_ = lean_box(0);
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = lean_string_utf8_next_fast(v_s_2035_, v___x_2036_);
v___x_2044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2044_, 0, v_s_2035_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
lean_ctor_set(v___x_2044_, 2, v___x_2037_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
return v___x_2045_;
}
}
else
{
lean_object* v___x_2046_; 
lean_dec_ref(v_s_2035_);
v___x_2046_ = lean_box(0);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_2047_, uint32_t v_pat_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_2050_, lean_object* v_pat_2051_){
_start:
{
uint32_t v_pat_boxed_2052_; lean_object* v_res_2053_; 
v_pat_boxed_2052_ = lean_unbox_uint32(v_pat_2051_);
lean_dec(v_pat_2051_);
v_res_2053_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_2050_, v_pat_boxed_2052_);
return v_res_2053_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_2054_, lean_object* v_as_2055_, size_t v_i_2056_, size_t v_stop_2057_){
_start:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_usize_dec_eq(v_i_2056_, v_stop_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_array_uget_borrowed(v_as_2055_, v_i_2056_);
v___x_2060_ = lean_name_eq(v_a_2054_, v___x_2059_);
if (v___x_2060_ == 0)
{
size_t v___x_2061_; size_t v___x_2062_; 
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2056_, v___x_2061_);
v_i_2056_ = v___x_2062_;
goto _start;
}
else
{
return v___x_2060_;
}
}
else
{
uint8_t v___x_2064_; 
v___x_2064_ = 0;
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_2065_, lean_object* v_as_2066_, lean_object* v_i_2067_, lean_object* v_stop_2068_){
_start:
{
size_t v_i_boxed_2069_; size_t v_stop_boxed_2070_; uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_i_boxed_2069_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_stop_boxed_2070_ = lean_unbox_usize(v_stop_2068_);
lean_dec(v_stop_2068_);
v_res_2071_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2065_, v_as_2066_, v_i_boxed_2069_, v_stop_boxed_2070_);
lean_dec_ref(v_as_2066_);
lean_dec(v_a_2065_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = lean_array_get_size(v_as_2073_);
v___x_2077_ = lean_nat_dec_lt(v___x_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
return v___x_2077_;
}
else
{
if (v___x_2077_ == 0)
{
return v___x_2077_;
}
else
{
size_t v___x_2078_; size_t v___x_2079_; uint8_t v___x_2080_; 
v___x_2078_ = ((size_t)0ULL);
v___x_2079_ = lean_usize_of_nat(v___x_2076_);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2074_, v_as_2073_, v___x_2078_, v___x_2079_);
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2081_, lean_object* v_a_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_as_2081_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_2085_, size_t v_i_2086_, size_t v_stop_2087_, lean_object* v_b_2088_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_usize_dec_eq(v_i_2086_, v_stop_2087_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; 
v___x_2090_ = lean_array_uget_borrowed(v_as_2085_, v_i_2086_);
v___x_2091_ = l_Array_append___redArg(v_b_2088_, v___x_2090_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_add(v_i_2086_, v___x_2092_);
v_i_2086_ = v___x_2093_;
v_b_2088_ = v___x_2091_;
goto _start;
}
else
{
return v_b_2088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_2095_, lean_object* v_i_2096_, lean_object* v_stop_2097_, lean_object* v_b_2098_){
_start:
{
size_t v_i_boxed_2099_; size_t v_stop_boxed_2100_; lean_object* v_res_2101_; 
v_i_boxed_2099_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_stop_boxed_2100_ = lean_unbox_usize(v_stop_2097_);
lean_dec(v_stop_2097_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_2095_, v_i_boxed_2099_, v_stop_boxed_2100_, v_b_2098_);
lean_dec_ref(v_as_2095_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2102_, lean_object* v_k_2103_, lean_object* v_fallback_2104_){
_start:
{
if (lean_obj_tag(v_t_2102_) == 0)
{
lean_object* v_k_2105_; lean_object* v_v_2106_; lean_object* v_l_2107_; lean_object* v_r_2108_; uint8_t v___x_2109_; 
v_k_2105_ = lean_ctor_get(v_t_2102_, 1);
v_v_2106_ = lean_ctor_get(v_t_2102_, 2);
v_l_2107_ = lean_ctor_get(v_t_2102_, 3);
v_r_2108_ = lean_ctor_get(v_t_2102_, 4);
v___x_2109_ = lean_string_compare(v_k_2103_, v_k_2105_);
switch(v___x_2109_)
{
case 0:
{
v_t_2102_ = v_l_2107_;
goto _start;
}
case 1:
{
lean_inc(v_v_2106_);
return v_v_2106_;
}
default: 
{
v_t_2102_ = v_r_2108_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2104_);
return v_fallback_2104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2112_, lean_object* v_k_2113_, lean_object* v_fallback_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2112_, v_k_2113_, v_fallback_2114_);
lean_dec(v_fallback_2114_);
lean_dec_ref(v_k_2113_);
lean_dec(v_t_2112_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2136_, lean_object* v_x_2137_){
_start:
{
lean_object* v___y_2139_; lean_object* v___y_2140_; uint8_t v___y_2141_; lean_object* v___y_2151_; lean_object* v___y_2152_; uint8_t v___y_2153_; lean_object* v___y_2163_; lean_object* v___y_2164_; uint8_t v___y_2165_; lean_object* v___y_2175_; lean_object* v___y_2176_; uint8_t v___y_2177_; lean_object* v___y_2187_; uint8_t v___y_2188_; uint8_t v___y_2189_; uint8_t v___y_2190_; lean_object* v___y_2191_; uint8_t v___y_2192_; uint8_t v___y_2194_; lean_object* v___y_2195_; uint8_t v___y_2196_; uint8_t v___y_2197_; lean_object* v___y_2198_; uint8_t v___y_2199_; lean_object* v___y_2201_; uint8_t v___y_2202_; uint8_t v___y_2203_; uint8_t v___y_2204_; uint32_t v___y_2205_; lean_object* v___y_2206_; uint8_t v___y_2211_; lean_object* v___y_2212_; uint8_t v___y_2213_; uint8_t v___y_2214_; uint32_t v___y_2215_; lean_object* v___y_2216_; uint8_t v___y_2217_; lean_object* v___y_2223_; lean_object* v___y_2224_; uint8_t v___y_2225_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2137_);
v___x_2235_ = l_Lean_Syntax_isOfKind(v_x_2137_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; uint8_t v___x_2237_; uint8_t v___y_2239_; uint8_t v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; uint8_t v___y_2243_; uint8_t v___y_2245_; uint8_t v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; uint8_t v___y_2249_; uint8_t v___y_2251_; uint8_t v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; uint32_t v___y_2255_; uint8_t v___y_2260_; uint8_t v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; uint32_t v___y_2264_; uint8_t v___y_2265_; 
v___x_2236_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2137_);
v___x_2237_ = l_Lean_Syntax_isOfKind(v_x_2137_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2137_);
v___x_2271_ = l_Lean_Syntax_getKind(v_x_2137_);
v___x_2272_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; uint8_t v___x_2274_; lean_object* v___y_2276_; lean_object* v___y_2277_; uint8_t v___y_2278_; lean_object* v___y_2280_; lean_object* v___y_2281_; uint8_t v___y_2282_; uint8_t v___y_2283_; lean_object* v___y_2285_; lean_object* v___y_2286_; uint8_t v___y_2287_; uint32_t v___y_2288_; lean_object* v___y_2293_; lean_object* v___y_2294_; uint8_t v___y_2295_; uint32_t v___y_2296_; uint8_t v___y_2297_; lean_object* v___y_2303_; lean_object* v___y_2304_; uint8_t v___y_2305_; lean_object* v___y_2320_; uint32_t v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2327_; uint32_t v___y_2328_; lean_object* v___y_2329_; uint8_t v___y_2330_; lean_object* v___y_2336_; 
v___x_2273_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2274_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2273_, v___x_2271_);
lean_dec(v___x_2271_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2137_);
v___x_2352_ = l_Lean_Syntax_isOfKind(v_x_2137_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; size_t v_sz_2354_; size_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2353_ = l_Lean_Syntax_getArgs(v_x_2137_);
v_sz_2354_ = lean_array_size(v___x_2353_);
v___x_2355_ = ((size_t)0ULL);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2136_, v_sz_2354_, v___x_2355_, v___x_2353_);
v___x_2357_ = lean_unsigned_to_nat(0u);
v___x_2358_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2359_ = lean_array_get_size(v___x_2356_);
v___x_2360_ = lean_nat_dec_lt(v___x_2357_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_dec_ref(v___x_2356_);
v___y_2336_ = v___x_2358_;
goto v___jp_2335_;
}
else
{
size_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_usize_of_nat(v___x_2359_);
v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2356_, v___x_2355_, v___x_2361_, v___x_2358_);
lean_dec_ref(v___x_2356_);
v___y_2336_ = v___x_2362_;
goto v___jp_2335_;
}
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2363_);
v___x_2365_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2136_, v___x_2364_);
v___y_2336_ = v___x_2365_;
goto v___jp_2335_;
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2366_);
lean_dec(v_x_2137_);
v___x_2368_ = l_Lean_Syntax_isAtom(v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_inc_ref(v_text_2136_);
v___x_2369_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2369_, 0, v_text_2136_);
v___x_2370_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2136_, v___x_2367_, v___x_2369_);
lean_dec_ref(v_text_2136_);
return v___x_2370_;
}
else
{
lean_object* v___x_2371_; 
lean_dec(v___x_2367_);
lean_dec_ref(v_text_2136_);
v___x_2371_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2371_;
}
}
v___jp_2275_:
{
if (v___y_2278_ == 0)
{
lean_dec_ref(v___y_2276_);
lean_dec(v_x_2137_);
return v___y_2277_;
}
else
{
v___y_2151_ = v___y_2276_;
v___y_2152_ = v___y_2277_;
v___y_2153_ = v___x_2274_;
goto v___jp_2150_;
}
}
v___jp_2279_:
{
if (v___y_2282_ == 0)
{
v___y_2276_ = v___y_2280_;
v___y_2277_ = v___y_2281_;
v___y_2278_ = v___y_2283_;
goto v___jp_2275_;
}
else
{
if (v___x_2274_ == 0)
{
v___y_2151_ = v___y_2280_;
v___y_2152_ = v___y_2281_;
v___y_2153_ = v___x_2274_;
goto v___jp_2150_;
}
else
{
v___y_2276_ = v___y_2280_;
v___y_2277_ = v___y_2281_;
v___y_2278_ = v___y_2283_;
goto v___jp_2275_;
}
}
}
v___jp_2284_:
{
uint32_t v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = 95;
v___x_2290_ = lean_uint32_dec_eq(v___y_2288_, v___x_2289_);
if (v___x_2290_ == 0)
{
uint8_t v___x_2291_; 
v___x_2291_ = l_Lean_isLetterLike(v___y_2288_);
v___y_2280_ = v___y_2285_;
v___y_2281_ = v___y_2286_;
v___y_2282_ = v___y_2287_;
v___y_2283_ = v___x_2291_;
goto v___jp_2279_;
}
else
{
v___y_2280_ = v___y_2285_;
v___y_2281_ = v___y_2286_;
v___y_2282_ = v___y_2287_;
v___y_2283_ = v___x_2290_;
goto v___jp_2279_;
}
}
v___jp_2292_:
{
if (v___y_2297_ == 0)
{
uint32_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = 97;
v___x_2299_ = lean_uint32_dec_le(v___x_2298_, v___y_2296_);
if (v___x_2299_ == 0)
{
v___y_2285_ = v___y_2293_;
v___y_2286_ = v___y_2294_;
v___y_2287_ = v___y_2295_;
v___y_2288_ = v___y_2296_;
goto v___jp_2284_;
}
else
{
uint32_t v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = 122;
v___x_2301_ = lean_uint32_dec_le(v___y_2296_, v___x_2300_);
if (v___x_2301_ == 0)
{
v___y_2285_ = v___y_2293_;
v___y_2286_ = v___y_2294_;
v___y_2287_ = v___y_2295_;
v___y_2288_ = v___y_2296_;
goto v___jp_2284_;
}
else
{
v___y_2280_ = v___y_2293_;
v___y_2281_ = v___y_2294_;
v___y_2282_ = v___y_2295_;
v___y_2283_ = v___x_2301_;
goto v___jp_2279_;
}
}
}
else
{
v___y_2280_ = v___y_2293_;
v___y_2281_ = v___y_2294_;
v___y_2282_ = v___y_2295_;
v___y_2283_ = v___y_2297_;
goto v___jp_2279_;
}
}
v___jp_2302_:
{
lean_object* v___x_2306_; 
lean_inc_ref(v___y_2303_);
v___x_2306_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2303_);
if (lean_obj_tag(v___x_2306_) == 0)
{
v___y_2280_ = v___y_2303_;
v___y_2281_ = v___y_2304_;
v___y_2282_ = v___y_2305_;
v___y_2283_ = v___x_2274_;
goto v___jp_2279_;
}
else
{
lean_object* v_val_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_val_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = l_String_Slice_Pos_get_x3f(v_val_2307_, v___x_2308_);
lean_dec(v_val_2307_);
if (lean_obj_tag(v___x_2309_) == 0)
{
v___y_2280_ = v___y_2303_;
v___y_2281_ = v___y_2304_;
v___y_2282_ = v___y_2305_;
v___y_2283_ = v___x_2274_;
goto v___jp_2279_;
}
else
{
lean_object* v_val_2310_; uint32_t v___x_2311_; uint32_t v___x_2312_; uint8_t v___x_2313_; 
v_val_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_val_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2311_ = 65;
v___x_2312_ = lean_unbox_uint32(v_val_2310_);
v___x_2313_ = lean_uint32_dec_le(v___x_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
uint32_t v___x_2314_; 
v___x_2314_ = lean_unbox_uint32(v_val_2310_);
lean_dec(v_val_2310_);
v___y_2293_ = v___y_2303_;
v___y_2294_ = v___y_2304_;
v___y_2295_ = v___y_2305_;
v___y_2296_ = v___x_2314_;
v___y_2297_ = v___x_2313_;
goto v___jp_2292_;
}
else
{
uint32_t v___x_2315_; uint32_t v___x_2316_; uint8_t v___x_2317_; uint32_t v___x_2318_; 
v___x_2315_ = 90;
v___x_2316_ = lean_unbox_uint32(v_val_2310_);
v___x_2317_ = lean_uint32_dec_le(v___x_2316_, v___x_2315_);
v___x_2318_ = lean_unbox_uint32(v_val_2310_);
lean_dec(v_val_2310_);
v___y_2293_ = v___y_2303_;
v___y_2294_ = v___y_2304_;
v___y_2295_ = v___y_2305_;
v___y_2296_ = v___x_2318_;
v___y_2297_ = v___x_2317_;
goto v___jp_2292_;
}
}
}
}
v___jp_2319_:
{
uint32_t v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = 95;
v___x_2324_ = lean_uint32_dec_eq(v___y_2321_, v___x_2323_);
if (v___x_2324_ == 0)
{
uint8_t v___x_2325_; 
v___x_2325_ = l_Lean_isLetterLike(v___y_2321_);
v___y_2303_ = v___y_2320_;
v___y_2304_ = v___y_2322_;
v___y_2305_ = v___x_2325_;
goto v___jp_2302_;
}
else
{
v___y_2303_ = v___y_2320_;
v___y_2304_ = v___y_2322_;
v___y_2305_ = v___x_2324_;
goto v___jp_2302_;
}
}
v___jp_2326_:
{
if (v___y_2330_ == 0)
{
uint32_t v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = 97;
v___x_2332_ = lean_uint32_dec_le(v___x_2331_, v___y_2328_);
if (v___x_2332_ == 0)
{
v___y_2320_ = v___y_2327_;
v___y_2321_ = v___y_2328_;
v___y_2322_ = v___y_2329_;
goto v___jp_2319_;
}
else
{
uint32_t v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = 122;
v___x_2334_ = lean_uint32_dec_le(v___y_2328_, v___x_2333_);
if (v___x_2334_ == 0)
{
v___y_2320_ = v___y_2327_;
v___y_2321_ = v___y_2328_;
v___y_2322_ = v___y_2329_;
goto v___jp_2319_;
}
else
{
v___y_2303_ = v___y_2327_;
v___y_2304_ = v___y_2329_;
v___y_2305_ = v___x_2334_;
goto v___jp_2302_;
}
}
}
else
{
v___y_2303_ = v___y_2327_;
v___y_2304_ = v___y_2329_;
v___y_2305_ = v___y_2330_;
goto v___jp_2302_;
}
}
v___jp_2335_:
{
if (lean_obj_tag(v_x_2137_) == 2)
{
lean_object* v_val_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_val_2337_ = lean_ctor_get(v_x_2137_, 1);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_string_utf8_byte_size(v_val_2337_);
lean_inc_ref(v_val_2337_);
v___x_2340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2340_, 0, v_val_2337_);
lean_ctor_set(v___x_2340_, 1, v___x_2338_);
lean_ctor_set(v___x_2340_, 2, v___x_2339_);
v___x_2341_ = l_String_Slice_Pos_get_x3f(v___x_2340_, v___x_2338_);
lean_dec_ref_known(v___x_2340_, 3);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_inc_ref(v_val_2337_);
v___y_2303_ = v_val_2337_;
v___y_2304_ = v___y_2336_;
v___y_2305_ = v___x_2274_;
goto v___jp_2302_;
}
else
{
lean_object* v_val_2342_; uint32_t v___x_2343_; uint32_t v___x_2344_; uint8_t v___x_2345_; 
v_val_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_val_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = 65;
v___x_2344_ = lean_unbox_uint32(v_val_2342_);
v___x_2345_ = lean_uint32_dec_le(v___x_2343_, v___x_2344_);
if (v___x_2345_ == 0)
{
uint32_t v___x_2346_; 
v___x_2346_ = lean_unbox_uint32(v_val_2342_);
lean_dec(v_val_2342_);
lean_inc_ref(v_val_2337_);
v___y_2327_ = v_val_2337_;
v___y_2328_ = v___x_2346_;
v___y_2329_ = v___y_2336_;
v___y_2330_ = v___x_2345_;
goto v___jp_2326_;
}
else
{
uint32_t v___x_2347_; uint32_t v___x_2348_; uint8_t v___x_2349_; uint32_t v___x_2350_; 
v___x_2347_ = 90;
v___x_2348_ = lean_unbox_uint32(v_val_2342_);
v___x_2349_ = lean_uint32_dec_le(v___x_2348_, v___x_2347_);
v___x_2350_ = lean_unbox_uint32(v_val_2342_);
lean_dec(v_val_2342_);
lean_inc_ref(v_val_2337_);
v___y_2327_ = v_val_2337_;
v___y_2328_ = v___x_2350_;
v___y_2329_ = v___y_2336_;
v___y_2330_ = v___x_2349_;
goto v___jp_2326_;
}
}
}
else
{
lean_dec(v_x_2137_);
return v___y_2336_;
}
}
}
else
{
lean_object* v___x_2372_; 
lean_dec(v___x_2271_);
lean_dec(v_x_2137_);
lean_dec_ref(v_text_2136_);
v___x_2372_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2372_;
}
}
else
{
lean_object* v___x_2373_; uint8_t v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; uint8_t v___y_2378_; uint8_t v___y_2392_; uint32_t v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2400_; uint32_t v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; uint8_t v___y_2404_; uint8_t v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2426_; uint8_t v___y_2427_; uint8_t v___y_2428_; lean_object* v___y_2429_; uint8_t v___y_2430_; lean_object* v___y_2444_; uint32_t v___y_2445_; uint8_t v___y_2446_; uint8_t v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2453_; uint32_t v___y_2454_; uint8_t v___y_2455_; uint8_t v___y_2456_; lean_object* v___y_2457_; uint8_t v___y_2458_; uint8_t v___y_2464_; uint8_t v___y_2465_; lean_object* v___y_2466_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2373_ = lean_unsigned_to_nat(0u);
v___x_2480_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2373_);
v___x_2481_ = lean_unsigned_to_nat(1u);
v___x_2482_ = lean_unsigned_to_nat(2u);
v___x_2483_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2482_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2483_);
v___x_2543_ = l_Lean_Syntax_isOfKind(v___x_2483_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
lean_dec(v___x_2483_);
v___x_2544_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2137_);
v___x_2545_ = l_Lean_Syntax_getKind(v_x_2137_);
v___x_2546_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___y_2550_; lean_object* v___y_2551_; uint8_t v___y_2552_; uint8_t v___y_2553_; uint8_t v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; uint8_t v___y_2558_; uint8_t v___y_2560_; uint32_t v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; uint8_t v___y_2568_; uint32_t v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2578_; lean_object* v___y_2579_; uint8_t v___y_2580_; uint32_t v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; uint32_t v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; uint8_t v___y_2604_; lean_object* v___y_2610_; 
v___x_2547_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2548_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2547_, v___x_2545_);
lean_dec(v___x_2545_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2137_);
v___x_2625_ = l_Lean_Syntax_isOfKind(v_x_2137_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; size_t v_sz_2627_; size_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
lean_dec(v___x_2480_);
v___x_2626_ = l_Lean_Syntax_getArgs(v_x_2137_);
v_sz_2627_ = lean_array_size(v___x_2626_);
v___x_2628_ = ((size_t)0ULL);
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2136_, v_sz_2627_, v___x_2628_, v___x_2626_);
v___x_2630_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2631_ = lean_array_get_size(v___x_2629_);
v___x_2632_ = lean_nat_dec_lt(v___x_2373_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_dec_ref(v___x_2629_);
v___y_2610_ = v___x_2630_;
goto v___jp_2609_;
}
else
{
size_t v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = lean_usize_of_nat(v___x_2631_);
v___x_2634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2629_, v___x_2628_, v___x_2633_, v___x_2630_);
lean_dec_ref(v___x_2629_);
v___y_2610_ = v___x_2634_;
goto v___jp_2609_;
}
}
else
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2136_, v___x_2480_);
v___y_2610_ = v___x_2635_;
goto v___jp_2609_;
}
}
else
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
lean_dec(v___x_2480_);
v___x_2636_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2481_);
lean_dec(v_x_2137_);
v___x_2637_ = l_Lean_Syntax_isAtom(v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_inc_ref(v_text_2136_);
v___x_2638_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2638_, 0, v_text_2136_);
v___x_2639_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2136_, v___x_2636_, v___x_2638_);
lean_dec_ref(v_text_2136_);
return v___x_2639_;
}
else
{
lean_object* v___x_2640_; 
lean_dec(v___x_2636_);
lean_dec_ref(v_text_2136_);
v___x_2640_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2640_;
}
}
v___jp_2549_:
{
if (v___y_2553_ == 0)
{
v___y_2223_ = v___y_2550_;
v___y_2224_ = v___y_2551_;
v___y_2225_ = v___x_2548_;
goto v___jp_2222_;
}
else
{
if (v___y_2552_ == 0)
{
v___y_2223_ = v___y_2550_;
v___y_2224_ = v___y_2551_;
v___y_2225_ = v___x_2237_;
goto v___jp_2222_;
}
else
{
v___y_2223_ = v___y_2550_;
v___y_2224_ = v___y_2551_;
v___y_2225_ = v___x_2548_;
goto v___jp_2222_;
}
}
}
v___jp_2554_:
{
if (v___y_2555_ == 0)
{
v___y_2550_ = v___y_2556_;
v___y_2551_ = v___y_2557_;
v___y_2552_ = v___y_2558_;
v___y_2553_ = v___x_2237_;
goto v___jp_2549_;
}
else
{
v___y_2550_ = v___y_2556_;
v___y_2551_ = v___y_2557_;
v___y_2552_ = v___y_2558_;
v___y_2553_ = v___x_2548_;
goto v___jp_2549_;
}
}
v___jp_2559_:
{
uint32_t v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = 95;
v___x_2565_ = lean_uint32_dec_eq(v___y_2561_, v___x_2564_);
if (v___x_2565_ == 0)
{
uint8_t v___x_2566_; 
v___x_2566_ = l_Lean_isLetterLike(v___y_2561_);
v___y_2555_ = v___y_2560_;
v___y_2556_ = v___y_2562_;
v___y_2557_ = v___y_2563_;
v___y_2558_ = v___x_2566_;
goto v___jp_2554_;
}
else
{
v___y_2555_ = v___y_2560_;
v___y_2556_ = v___y_2562_;
v___y_2557_ = v___y_2563_;
v___y_2558_ = v___x_2565_;
goto v___jp_2554_;
}
}
v___jp_2567_:
{
if (v___y_2572_ == 0)
{
uint32_t v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = 97;
v___x_2574_ = lean_uint32_dec_le(v___x_2573_, v___y_2569_);
if (v___x_2574_ == 0)
{
v___y_2560_ = v___y_2568_;
v___y_2561_ = v___y_2569_;
v___y_2562_ = v___y_2570_;
v___y_2563_ = v___y_2571_;
goto v___jp_2559_;
}
else
{
uint32_t v___x_2575_; uint8_t v___x_2576_; 
v___x_2575_ = 122;
v___x_2576_ = lean_uint32_dec_le(v___y_2569_, v___x_2575_);
if (v___x_2576_ == 0)
{
v___y_2560_ = v___y_2568_;
v___y_2561_ = v___y_2569_;
v___y_2562_ = v___y_2570_;
v___y_2563_ = v___y_2571_;
goto v___jp_2559_;
}
else
{
v___y_2555_ = v___y_2568_;
v___y_2556_ = v___y_2570_;
v___y_2557_ = v___y_2571_;
v___y_2558_ = v___x_2576_;
goto v___jp_2554_;
}
}
}
else
{
v___y_2555_ = v___y_2568_;
v___y_2556_ = v___y_2570_;
v___y_2557_ = v___y_2571_;
v___y_2558_ = v___y_2572_;
goto v___jp_2554_;
}
}
v___jp_2577_:
{
lean_object* v___x_2581_; 
lean_inc_ref(v___y_2578_);
v___x_2581_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2578_);
if (lean_obj_tag(v___x_2581_) == 0)
{
v___y_2555_ = v___y_2580_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2579_;
v___y_2558_ = v___x_2548_;
goto v___jp_2554_;
}
else
{
lean_object* v_val_2582_; lean_object* v___x_2583_; 
v_val_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_val_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = l_String_Slice_Pos_get_x3f(v_val_2582_, v___x_2373_);
lean_dec(v_val_2582_);
if (lean_obj_tag(v___x_2583_) == 0)
{
v___y_2555_ = v___y_2580_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2579_;
v___y_2558_ = v___x_2548_;
goto v___jp_2554_;
}
else
{
lean_object* v_val_2584_; uint32_t v___x_2585_; uint32_t v___x_2586_; uint8_t v___x_2587_; 
v_val_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = 65;
v___x_2586_ = lean_unbox_uint32(v_val_2584_);
v___x_2587_ = lean_uint32_dec_le(v___x_2585_, v___x_2586_);
if (v___x_2587_ == 0)
{
uint32_t v___x_2588_; 
v___x_2588_ = lean_unbox_uint32(v_val_2584_);
lean_dec(v_val_2584_);
v___y_2568_ = v___y_2580_;
v___y_2569_ = v___x_2588_;
v___y_2570_ = v___y_2578_;
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___x_2587_;
goto v___jp_2567_;
}
else
{
uint32_t v___x_2589_; uint32_t v___x_2590_; uint8_t v___x_2591_; uint32_t v___x_2592_; 
v___x_2589_ = 90;
v___x_2590_ = lean_unbox_uint32(v_val_2584_);
v___x_2591_ = lean_uint32_dec_le(v___x_2590_, v___x_2589_);
v___x_2592_ = lean_unbox_uint32(v_val_2584_);
lean_dec(v_val_2584_);
v___y_2568_ = v___y_2580_;
v___y_2569_ = v___x_2592_;
v___y_2570_ = v___y_2578_;
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___x_2591_;
goto v___jp_2567_;
}
}
}
}
v___jp_2593_:
{
uint32_t v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = 95;
v___x_2598_ = lean_uint32_dec_eq(v___y_2594_, v___x_2597_);
if (v___x_2598_ == 0)
{
uint8_t v___x_2599_; 
v___x_2599_ = l_Lean_isLetterLike(v___y_2594_);
v___y_2578_ = v___y_2595_;
v___y_2579_ = v___y_2596_;
v___y_2580_ = v___x_2599_;
goto v___jp_2577_;
}
else
{
v___y_2578_ = v___y_2595_;
v___y_2579_ = v___y_2596_;
v___y_2580_ = v___x_2598_;
goto v___jp_2577_;
}
}
v___jp_2600_:
{
if (v___y_2604_ == 0)
{
uint32_t v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = 97;
v___x_2606_ = lean_uint32_dec_le(v___x_2605_, v___y_2601_);
if (v___x_2606_ == 0)
{
v___y_2594_ = v___y_2601_;
v___y_2595_ = v___y_2602_;
v___y_2596_ = v___y_2603_;
goto v___jp_2593_;
}
else
{
uint32_t v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = 122;
v___x_2608_ = lean_uint32_dec_le(v___y_2601_, v___x_2607_);
if (v___x_2608_ == 0)
{
v___y_2594_ = v___y_2601_;
v___y_2595_ = v___y_2602_;
v___y_2596_ = v___y_2603_;
goto v___jp_2593_;
}
else
{
v___y_2578_ = v___y_2602_;
v___y_2579_ = v___y_2603_;
v___y_2580_ = v___x_2608_;
goto v___jp_2577_;
}
}
}
else
{
v___y_2578_ = v___y_2602_;
v___y_2579_ = v___y_2603_;
v___y_2580_ = v___y_2604_;
goto v___jp_2577_;
}
}
v___jp_2609_:
{
if (lean_obj_tag(v_x_2137_) == 2)
{
lean_object* v_val_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_val_2611_ = lean_ctor_get(v_x_2137_, 1);
v___x_2612_ = lean_string_utf8_byte_size(v_val_2611_);
lean_inc_ref(v_val_2611_);
v___x_2613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2613_, 0, v_val_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2373_);
lean_ctor_set(v___x_2613_, 2, v___x_2612_);
v___x_2614_ = l_String_Slice_Pos_get_x3f(v___x_2613_, v___x_2373_);
lean_dec_ref_known(v___x_2613_, 3);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_inc_ref(v_val_2611_);
v___y_2578_ = v_val_2611_;
v___y_2579_ = v___y_2610_;
v___y_2580_ = v___x_2548_;
goto v___jp_2577_;
}
else
{
lean_object* v_val_2615_; uint32_t v___x_2616_; uint32_t v___x_2617_; uint8_t v___x_2618_; 
v_val_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_val_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = 65;
v___x_2617_ = lean_unbox_uint32(v_val_2615_);
v___x_2618_ = lean_uint32_dec_le(v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
uint32_t v___x_2619_; 
v___x_2619_ = lean_unbox_uint32(v_val_2615_);
lean_dec(v_val_2615_);
lean_inc_ref(v_val_2611_);
v___y_2601_ = v___x_2619_;
v___y_2602_ = v_val_2611_;
v___y_2603_ = v___y_2610_;
v___y_2604_ = v___x_2618_;
goto v___jp_2600_;
}
else
{
uint32_t v___x_2620_; uint32_t v___x_2621_; uint8_t v___x_2622_; uint32_t v___x_2623_; 
v___x_2620_ = 90;
v___x_2621_ = lean_unbox_uint32(v_val_2615_);
v___x_2622_ = lean_uint32_dec_le(v___x_2621_, v___x_2620_);
v___x_2623_ = lean_unbox_uint32(v_val_2615_);
lean_dec(v_val_2615_);
lean_inc_ref(v_val_2611_);
v___y_2601_ = v___x_2623_;
v___y_2602_ = v_val_2611_;
v___y_2603_ = v___y_2610_;
v___y_2604_ = v___x_2622_;
goto v___jp_2600_;
}
}
}
else
{
lean_dec(v_x_2137_);
return v___y_2610_;
}
}
}
else
{
lean_object* v___x_2641_; 
lean_dec(v___x_2545_);
lean_dec(v___x_2480_);
lean_dec(v_x_2137_);
lean_dec_ref(v_text_2136_);
v___x_2641_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2641_;
}
}
else
{
goto v___jp_2484_;
}
}
else
{
goto v___jp_2484_;
}
v___jp_2374_:
{
lean_object* v___x_2379_; 
lean_inc_ref(v___y_2377_);
v___x_2379_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2377_);
if (lean_obj_tag(v___x_2379_) == 0)
{
v___y_2245_ = v___y_2378_;
v___y_2246_ = v___y_2375_;
v___y_2247_ = v___y_2376_;
v___y_2248_ = v___y_2377_;
v___y_2249_ = v___y_2375_;
goto v___jp_2244_;
}
else
{
lean_object* v_val_2380_; lean_object* v___x_2381_; 
v_val_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_val_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = l_String_Slice_Pos_get_x3f(v_val_2380_, v___x_2373_);
lean_dec(v_val_2380_);
if (lean_obj_tag(v___x_2381_) == 0)
{
v___y_2245_ = v___y_2378_;
v___y_2246_ = v___y_2375_;
v___y_2247_ = v___y_2376_;
v___y_2248_ = v___y_2377_;
v___y_2249_ = v___y_2375_;
goto v___jp_2244_;
}
else
{
lean_object* v_val_2382_; uint32_t v___x_2383_; uint32_t v___x_2384_; uint8_t v___x_2385_; 
v_val_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2383_ = 65;
v___x_2384_ = lean_unbox_uint32(v_val_2382_);
v___x_2385_ = lean_uint32_dec_le(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
uint32_t v___x_2386_; 
v___x_2386_ = lean_unbox_uint32(v_val_2382_);
lean_dec(v_val_2382_);
v___y_2260_ = v___y_2378_;
v___y_2261_ = v___y_2375_;
v___y_2262_ = v___y_2376_;
v___y_2263_ = v___y_2377_;
v___y_2264_ = v___x_2386_;
v___y_2265_ = v___x_2385_;
goto v___jp_2259_;
}
else
{
uint32_t v___x_2387_; uint32_t v___x_2388_; uint8_t v___x_2389_; uint32_t v___x_2390_; 
v___x_2387_ = 90;
v___x_2388_ = lean_unbox_uint32(v_val_2382_);
v___x_2389_ = lean_uint32_dec_le(v___x_2388_, v___x_2387_);
v___x_2390_ = lean_unbox_uint32(v_val_2382_);
lean_dec(v_val_2382_);
v___y_2260_ = v___y_2378_;
v___y_2261_ = v___y_2375_;
v___y_2262_ = v___y_2376_;
v___y_2263_ = v___y_2377_;
v___y_2264_ = v___x_2390_;
v___y_2265_ = v___x_2389_;
goto v___jp_2259_;
}
}
}
}
v___jp_2391_:
{
uint32_t v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = 95;
v___x_2397_ = lean_uint32_dec_eq(v___y_2393_, v___x_2396_);
if (v___x_2397_ == 0)
{
uint8_t v___x_2398_; 
v___x_2398_ = l_Lean_isLetterLike(v___y_2393_);
v___y_2375_ = v___y_2392_;
v___y_2376_ = v___y_2394_;
v___y_2377_ = v___y_2395_;
v___y_2378_ = v___x_2398_;
goto v___jp_2374_;
}
else
{
v___y_2375_ = v___y_2392_;
v___y_2376_ = v___y_2394_;
v___y_2377_ = v___y_2395_;
v___y_2378_ = v___x_2397_;
goto v___jp_2374_;
}
}
v___jp_2399_:
{
if (v___y_2404_ == 0)
{
uint32_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = 97;
v___x_2406_ = lean_uint32_dec_le(v___x_2405_, v___y_2401_);
if (v___x_2406_ == 0)
{
v___y_2392_ = v___y_2400_;
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2402_;
v___y_2395_ = v___y_2403_;
goto v___jp_2391_;
}
else
{
uint32_t v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = 122;
v___x_2408_ = lean_uint32_dec_le(v___y_2401_, v___x_2407_);
if (v___x_2408_ == 0)
{
v___y_2392_ = v___y_2400_;
v___y_2393_ = v___y_2401_;
v___y_2394_ = v___y_2402_;
v___y_2395_ = v___y_2403_;
goto v___jp_2391_;
}
else
{
v___y_2375_ = v___y_2400_;
v___y_2376_ = v___y_2402_;
v___y_2377_ = v___y_2403_;
v___y_2378_ = v___x_2408_;
goto v___jp_2374_;
}
}
}
else
{
v___y_2375_ = v___y_2400_;
v___y_2376_ = v___y_2402_;
v___y_2377_ = v___y_2403_;
v___y_2378_ = v___y_2404_;
goto v___jp_2374_;
}
}
v___jp_2409_:
{
if (lean_obj_tag(v_x_2137_) == 2)
{
lean_object* v_val_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_val_2412_ = lean_ctor_get(v_x_2137_, 1);
v___x_2413_ = lean_string_utf8_byte_size(v_val_2412_);
lean_inc_ref(v_val_2412_);
v___x_2414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2414_, 0, v_val_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2373_);
lean_ctor_set(v___x_2414_, 2, v___x_2413_);
v___x_2415_ = l_String_Slice_Pos_get_x3f(v___x_2414_, v___x_2373_);
lean_dec_ref_known(v___x_2414_, 3);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_inc_ref(v_val_2412_);
v___y_2375_ = v___y_2410_;
v___y_2376_ = v___y_2411_;
v___y_2377_ = v_val_2412_;
v___y_2378_ = v___y_2410_;
goto v___jp_2374_;
}
else
{
lean_object* v_val_2416_; uint32_t v___x_2417_; uint32_t v___x_2418_; uint8_t v___x_2419_; 
v_val_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_val_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2417_ = 65;
v___x_2418_ = lean_unbox_uint32(v_val_2416_);
v___x_2419_ = lean_uint32_dec_le(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
uint32_t v___x_2420_; 
v___x_2420_ = lean_unbox_uint32(v_val_2416_);
lean_dec(v_val_2416_);
lean_inc_ref(v_val_2412_);
v___y_2400_ = v___y_2410_;
v___y_2401_ = v___x_2420_;
v___y_2402_ = v___y_2411_;
v___y_2403_ = v_val_2412_;
v___y_2404_ = v___x_2419_;
goto v___jp_2399_;
}
else
{
uint32_t v___x_2421_; uint32_t v___x_2422_; uint8_t v___x_2423_; uint32_t v___x_2424_; 
v___x_2421_ = 90;
v___x_2422_ = lean_unbox_uint32(v_val_2416_);
v___x_2423_ = lean_uint32_dec_le(v___x_2422_, v___x_2421_);
v___x_2424_ = lean_unbox_uint32(v_val_2416_);
lean_dec(v_val_2416_);
lean_inc_ref(v_val_2412_);
v___y_2400_ = v___y_2410_;
v___y_2401_ = v___x_2424_;
v___y_2402_ = v___y_2411_;
v___y_2403_ = v_val_2412_;
v___y_2404_ = v___x_2423_;
goto v___jp_2399_;
}
}
}
else
{
lean_dec(v_x_2137_);
return v___y_2411_;
}
}
v___jp_2425_:
{
lean_object* v___x_2431_; 
lean_inc_ref(v___y_2429_);
v___x_2431_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2429_);
if (lean_obj_tag(v___x_2431_) == 0)
{
v___y_2194_ = v___y_2430_;
v___y_2195_ = v___y_2426_;
v___y_2196_ = v___y_2427_;
v___y_2197_ = v___y_2428_;
v___y_2198_ = v___y_2429_;
v___y_2199_ = v___y_2427_;
goto v___jp_2193_;
}
else
{
lean_object* v_val_2432_; lean_object* v___x_2433_; 
v_val_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_val_2432_);
lean_dec_ref_known(v___x_2431_, 1);
v___x_2433_ = l_String_Slice_Pos_get_x3f(v_val_2432_, v___x_2373_);
lean_dec(v_val_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
v___y_2194_ = v___y_2430_;
v___y_2195_ = v___y_2426_;
v___y_2196_ = v___y_2427_;
v___y_2197_ = v___y_2428_;
v___y_2198_ = v___y_2429_;
v___y_2199_ = v___y_2427_;
goto v___jp_2193_;
}
else
{
lean_object* v_val_2434_; uint32_t v___x_2435_; uint32_t v___x_2436_; uint8_t v___x_2437_; 
v_val_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_val_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v___x_2435_ = 65;
v___x_2436_ = lean_unbox_uint32(v_val_2434_);
v___x_2437_ = lean_uint32_dec_le(v___x_2435_, v___x_2436_);
if (v___x_2437_ == 0)
{
uint32_t v___x_2438_; 
v___x_2438_ = lean_unbox_uint32(v_val_2434_);
lean_dec(v_val_2434_);
v___y_2211_ = v___y_2430_;
v___y_2212_ = v___y_2426_;
v___y_2213_ = v___y_2427_;
v___y_2214_ = v___y_2428_;
v___y_2215_ = v___x_2438_;
v___y_2216_ = v___y_2429_;
v___y_2217_ = v___x_2437_;
goto v___jp_2210_;
}
else
{
uint32_t v___x_2439_; uint32_t v___x_2440_; uint8_t v___x_2441_; uint32_t v___x_2442_; 
v___x_2439_ = 90;
v___x_2440_ = lean_unbox_uint32(v_val_2434_);
v___x_2441_ = lean_uint32_dec_le(v___x_2440_, v___x_2439_);
v___x_2442_ = lean_unbox_uint32(v_val_2434_);
lean_dec(v_val_2434_);
v___y_2211_ = v___y_2430_;
v___y_2212_ = v___y_2426_;
v___y_2213_ = v___y_2427_;
v___y_2214_ = v___y_2428_;
v___y_2215_ = v___x_2442_;
v___y_2216_ = v___y_2429_;
v___y_2217_ = v___x_2441_;
goto v___jp_2210_;
}
}
}
}
v___jp_2443_:
{
uint32_t v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = 95;
v___x_2450_ = lean_uint32_dec_eq(v___y_2445_, v___x_2449_);
if (v___x_2450_ == 0)
{
uint8_t v___x_2451_; 
v___x_2451_ = l_Lean_isLetterLike(v___y_2445_);
v___y_2426_ = v___y_2444_;
v___y_2427_ = v___y_2446_;
v___y_2428_ = v___y_2447_;
v___y_2429_ = v___y_2448_;
v___y_2430_ = v___x_2451_;
goto v___jp_2425_;
}
else
{
v___y_2426_ = v___y_2444_;
v___y_2427_ = v___y_2446_;
v___y_2428_ = v___y_2447_;
v___y_2429_ = v___y_2448_;
v___y_2430_ = v___x_2450_;
goto v___jp_2425_;
}
}
v___jp_2452_:
{
if (v___y_2458_ == 0)
{
uint32_t v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = 97;
v___x_2460_ = lean_uint32_dec_le(v___x_2459_, v___y_2454_);
if (v___x_2460_ == 0)
{
v___y_2444_ = v___y_2453_;
v___y_2445_ = v___y_2454_;
v___y_2446_ = v___y_2455_;
v___y_2447_ = v___y_2456_;
v___y_2448_ = v___y_2457_;
goto v___jp_2443_;
}
else
{
uint32_t v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = 122;
v___x_2462_ = lean_uint32_dec_le(v___y_2454_, v___x_2461_);
if (v___x_2462_ == 0)
{
v___y_2444_ = v___y_2453_;
v___y_2445_ = v___y_2454_;
v___y_2446_ = v___y_2455_;
v___y_2447_ = v___y_2456_;
v___y_2448_ = v___y_2457_;
goto v___jp_2443_;
}
else
{
v___y_2426_ = v___y_2453_;
v___y_2427_ = v___y_2455_;
v___y_2428_ = v___y_2456_;
v___y_2429_ = v___y_2457_;
v___y_2430_ = v___x_2462_;
goto v___jp_2425_;
}
}
}
else
{
v___y_2426_ = v___y_2453_;
v___y_2427_ = v___y_2455_;
v___y_2428_ = v___y_2456_;
v___y_2429_ = v___y_2457_;
v___y_2430_ = v___y_2458_;
goto v___jp_2425_;
}
}
v___jp_2463_:
{
if (lean_obj_tag(v_x_2137_) == 2)
{
lean_object* v_val_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_val_2467_ = lean_ctor_get(v_x_2137_, 1);
v___x_2468_ = lean_string_utf8_byte_size(v_val_2467_);
lean_inc_ref(v_val_2467_);
v___x_2469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2469_, 0, v_val_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2373_);
lean_ctor_set(v___x_2469_, 2, v___x_2468_);
v___x_2470_ = l_String_Slice_Pos_get_x3f(v___x_2469_, v___x_2373_);
lean_dec_ref_known(v___x_2469_, 3);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_inc_ref(v_val_2467_);
v___y_2426_ = v___y_2466_;
v___y_2427_ = v___y_2464_;
v___y_2428_ = v___y_2465_;
v___y_2429_ = v_val_2467_;
v___y_2430_ = v___y_2464_;
goto v___jp_2425_;
}
else
{
lean_object* v_val_2471_; uint32_t v___x_2472_; uint32_t v___x_2473_; uint8_t v___x_2474_; 
v_val_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2472_ = 65;
v___x_2473_ = lean_unbox_uint32(v_val_2471_);
v___x_2474_ = lean_uint32_dec_le(v___x_2472_, v___x_2473_);
if (v___x_2474_ == 0)
{
uint32_t v___x_2475_; 
v___x_2475_ = lean_unbox_uint32(v_val_2471_);
lean_dec(v_val_2471_);
lean_inc_ref(v_val_2467_);
v___y_2453_ = v___y_2466_;
v___y_2454_ = v___x_2475_;
v___y_2455_ = v___y_2464_;
v___y_2456_ = v___y_2465_;
v___y_2457_ = v_val_2467_;
v___y_2458_ = v___x_2474_;
goto v___jp_2452_;
}
else
{
uint32_t v___x_2476_; uint32_t v___x_2477_; uint8_t v___x_2478_; uint32_t v___x_2479_; 
v___x_2476_ = 90;
v___x_2477_ = lean_unbox_uint32(v_val_2471_);
v___x_2478_ = lean_uint32_dec_le(v___x_2477_, v___x_2476_);
v___x_2479_ = lean_unbox_uint32(v_val_2471_);
lean_dec(v_val_2471_);
lean_inc_ref(v_val_2467_);
v___y_2453_ = v___y_2466_;
v___y_2454_ = v___x_2479_;
v___y_2455_ = v___y_2464_;
v___y_2456_ = v___y_2465_;
v___y_2457_ = v_val_2467_;
v___y_2458_ = v___x_2478_;
goto v___jp_2452_;
}
}
}
else
{
lean_dec(v_x_2137_);
return v___y_2466_;
}
}
v___jp_2484_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2485_ = lean_unsigned_to_nat(3u);
v___x_2486_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2485_);
v___x_2487_ = l_Lean_Syntax_matchesNull(v___x_2486_, v___x_2373_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
lean_dec(v___x_2483_);
v___x_2488_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2137_);
v___x_2489_ = l_Lean_Syntax_getKind(v_x_2137_);
v___x_2490_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2488_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2491_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2492_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2491_, v___x_2489_);
lean_dec(v___x_2489_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2137_);
v___x_2494_ = l_Lean_Syntax_isOfKind(v_x_2137_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; size_t v_sz_2496_; size_t v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
lean_dec(v___x_2480_);
v___x_2495_ = l_Lean_Syntax_getArgs(v_x_2137_);
v_sz_2496_ = lean_array_size(v___x_2495_);
v___x_2497_ = ((size_t)0ULL);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2136_, v_sz_2496_, v___x_2497_, v___x_2495_);
v___x_2499_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2500_ = lean_array_get_size(v___x_2498_);
v___x_2501_ = lean_nat_dec_lt(v___x_2373_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_dec_ref(v___x_2498_);
v___y_2410_ = v___x_2492_;
v___y_2411_ = v___x_2499_;
goto v___jp_2409_;
}
else
{
size_t v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_usize_of_nat(v___x_2500_);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2498_, v___x_2497_, v___x_2502_, v___x_2499_);
lean_dec_ref(v___x_2498_);
v___y_2410_ = v___x_2492_;
v___y_2411_ = v___x_2503_;
goto v___jp_2409_;
}
}
else
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2136_, v___x_2480_);
v___y_2410_ = v___x_2492_;
v___y_2411_ = v___x_2504_;
goto v___jp_2409_;
}
}
else
{
lean_object* v___x_2505_; uint8_t v___x_2506_; 
lean_dec(v___x_2480_);
v___x_2505_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2481_);
lean_dec(v_x_2137_);
v___x_2506_ = l_Lean_Syntax_isAtom(v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_inc_ref(v_text_2136_);
v___x_2507_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2507_, 0, v_text_2136_);
v___x_2508_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2136_, v___x_2505_, v___x_2507_);
lean_dec_ref(v_text_2136_);
return v___x_2508_;
}
else
{
lean_object* v___x_2509_; 
lean_dec(v___x_2505_);
lean_dec_ref(v_text_2136_);
v___x_2509_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2509_;
}
}
}
else
{
lean_object* v___x_2510_; 
lean_dec(v___x_2489_);
lean_dec(v___x_2480_);
lean_dec(v_x_2137_);
lean_dec_ref(v_text_2136_);
v___x_2510_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2510_;
}
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2511_ = lean_unsigned_to_nat(4u);
v___x_2512_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2511_);
v___x_2513_ = l_Lean_Syntax_matchesNull(v___x_2512_, v___x_2373_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
lean_dec(v___x_2483_);
v___x_2514_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2137_);
v___x_2515_ = l_Lean_Syntax_getKind(v_x_2137_);
v___x_2516_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2518_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2517_, v___x_2515_);
lean_dec(v___x_2515_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2137_);
v___x_2520_ = l_Lean_Syntax_isOfKind(v_x_2137_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; size_t v_sz_2522_; size_t v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
lean_dec(v___x_2480_);
v___x_2521_ = l_Lean_Syntax_getArgs(v_x_2137_);
v_sz_2522_ = lean_array_size(v___x_2521_);
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2136_, v_sz_2522_, v___x_2523_, v___x_2521_);
v___x_2525_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2526_ = lean_array_get_size(v___x_2524_);
v___x_2527_ = lean_nat_dec_lt(v___x_2373_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_dec_ref(v___x_2524_);
v___y_2464_ = v___x_2518_;
v___y_2465_ = v___x_2487_;
v___y_2466_ = v___x_2525_;
goto v___jp_2463_;
}
else
{
size_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_usize_of_nat(v___x_2526_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2524_, v___x_2523_, v___x_2528_, v___x_2525_);
lean_dec_ref(v___x_2524_);
v___y_2464_ = v___x_2518_;
v___y_2465_ = v___x_2487_;
v___y_2466_ = v___x_2529_;
goto v___jp_2463_;
}
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2136_, v___x_2480_);
v___y_2464_ = v___x_2518_;
v___y_2465_ = v___x_2487_;
v___y_2466_ = v___x_2530_;
goto v___jp_2463_;
}
}
else
{
lean_object* v___x_2531_; uint8_t v___x_2532_; 
lean_dec(v___x_2480_);
v___x_2531_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2481_);
lean_dec(v_x_2137_);
v___x_2532_ = l_Lean_Syntax_isAtom(v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_inc_ref(v_text_2136_);
v___x_2533_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2533_, 0, v_text_2136_);
v___x_2534_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2136_, v___x_2531_, v___x_2533_);
lean_dec_ref(v_text_2136_);
return v___x_2534_;
}
else
{
lean_object* v___x_2535_; 
lean_dec(v___x_2531_);
lean_dec_ref(v_text_2136_);
v___x_2535_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2535_;
}
}
}
else
{
lean_object* v___x_2536_; 
lean_dec(v___x_2515_);
lean_dec(v___x_2480_);
lean_dec(v_x_2137_);
lean_dec_ref(v_text_2136_);
v___x_2536_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2536_;
}
}
else
{
lean_object* v_tokens_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_dec(v_x_2137_);
v_tokens_2537_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2136_, v___x_2480_);
v___x_2538_ = 2;
v___x_2539_ = lean_unsigned_to_nat(5u);
v___x_2540_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2540_, 0, v___x_2483_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*2, v___x_2538_);
v___x_2541_ = lean_array_push(v_tokens_2537_, v___x_2540_);
return v___x_2541_;
}
}
}
}
v___jp_2238_:
{
if (v___y_2243_ == 0)
{
v___y_2163_ = v___y_2241_;
v___y_2164_ = v___y_2242_;
v___y_2165_ = v___y_2239_;
goto v___jp_2162_;
}
else
{
if (v___y_2240_ == 0)
{
v___y_2163_ = v___y_2241_;
v___y_2164_ = v___y_2242_;
v___y_2165_ = v___x_2237_;
goto v___jp_2162_;
}
else
{
v___y_2163_ = v___y_2241_;
v___y_2164_ = v___y_2242_;
v___y_2165_ = v___y_2239_;
goto v___jp_2162_;
}
}
}
v___jp_2244_:
{
if (v___y_2245_ == 0)
{
v___y_2239_ = v___y_2246_;
v___y_2240_ = v___y_2249_;
v___y_2241_ = v___y_2247_;
v___y_2242_ = v___y_2248_;
v___y_2243_ = v___x_2237_;
goto v___jp_2238_;
}
else
{
v___y_2239_ = v___y_2246_;
v___y_2240_ = v___y_2249_;
v___y_2241_ = v___y_2247_;
v___y_2242_ = v___y_2248_;
v___y_2243_ = v___y_2246_;
goto v___jp_2238_;
}
}
v___jp_2250_:
{
uint32_t v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = 95;
v___x_2257_ = lean_uint32_dec_eq(v___y_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
uint8_t v___x_2258_; 
v___x_2258_ = l_Lean_isLetterLike(v___y_2255_);
v___y_2245_ = v___y_2251_;
v___y_2246_ = v___y_2252_;
v___y_2247_ = v___y_2253_;
v___y_2248_ = v___y_2254_;
v___y_2249_ = v___x_2258_;
goto v___jp_2244_;
}
else
{
v___y_2245_ = v___y_2251_;
v___y_2246_ = v___y_2252_;
v___y_2247_ = v___y_2253_;
v___y_2248_ = v___y_2254_;
v___y_2249_ = v___x_2257_;
goto v___jp_2244_;
}
}
v___jp_2259_:
{
if (v___y_2265_ == 0)
{
uint32_t v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = 97;
v___x_2267_ = lean_uint32_dec_le(v___x_2266_, v___y_2264_);
if (v___x_2267_ == 0)
{
v___y_2251_ = v___y_2260_;
v___y_2252_ = v___y_2261_;
v___y_2253_ = v___y_2262_;
v___y_2254_ = v___y_2263_;
v___y_2255_ = v___y_2264_;
goto v___jp_2250_;
}
else
{
uint32_t v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = 122;
v___x_2269_ = lean_uint32_dec_le(v___y_2264_, v___x_2268_);
if (v___x_2269_ == 0)
{
v___y_2251_ = v___y_2260_;
v___y_2252_ = v___y_2261_;
v___y_2253_ = v___y_2262_;
v___y_2254_ = v___y_2263_;
v___y_2255_ = v___y_2264_;
goto v___jp_2250_;
}
else
{
v___y_2245_ = v___y_2260_;
v___y_2246_ = v___y_2261_;
v___y_2247_ = v___y_2262_;
v___y_2248_ = v___y_2263_;
v___y_2249_ = v___x_2269_;
goto v___jp_2244_;
}
}
}
else
{
v___y_2245_ = v___y_2260_;
v___y_2246_ = v___y_2261_;
v___y_2247_ = v___y_2262_;
v___y_2248_ = v___y_2263_;
v___y_2249_ = v___y_2265_;
goto v___jp_2244_;
}
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_unsigned_to_nat(2u);
v___x_2644_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2643_);
v___x_2645_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2644_);
v___x_2646_ = l_Lean_Syntax_isOfKind(v___x_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
lean_dec(v___x_2644_);
v___x_2647_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2137_);
v___x_2648_ = l_Lean_Syntax_getKind(v_x_2137_);
v___x_2649_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; uint8_t v___x_2651_; uint8_t v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2656_; uint8_t v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; uint8_t v___y_2661_; uint32_t v___y_2663_; uint8_t v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; uint32_t v___y_2671_; uint8_t v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; uint8_t v___y_2675_; lean_object* v___y_2681_; lean_object* v___y_2682_; uint8_t v___y_2683_; uint32_t v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; uint32_t v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; uint8_t v___y_2707_; lean_object* v___y_2713_; 
v___x_2650_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2651_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2650_, v___x_2648_);
lean_dec(v___x_2648_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2137_);
v___x_2728_ = l_Lean_Syntax_isOfKind(v_x_2137_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; size_t v_sz_2730_; size_t v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2729_ = l_Lean_Syntax_getArgs(v_x_2137_);
v_sz_2730_ = lean_array_size(v___x_2729_);
v___x_2731_ = ((size_t)0ULL);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2136_, v_sz_2730_, v___x_2731_, v___x_2729_);
v___x_2733_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2734_ = lean_array_get_size(v___x_2732_);
v___x_2735_ = lean_nat_dec_lt(v___x_2642_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_dec_ref(v___x_2732_);
v___y_2713_ = v___x_2733_;
goto v___jp_2712_;
}
else
{
size_t v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_usize_of_nat(v___x_2734_);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2732_, v___x_2731_, v___x_2736_, v___x_2733_);
lean_dec_ref(v___x_2732_);
v___y_2713_ = v___x_2737_;
goto v___jp_2712_;
}
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2642_);
v___x_2739_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2136_, v___x_2738_);
v___y_2713_ = v___x_2739_;
goto v___jp_2712_;
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2740_ = lean_unsigned_to_nat(1u);
v___x_2741_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2740_);
lean_dec(v_x_2137_);
v___x_2742_ = l_Lean_Syntax_isAtom(v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_inc_ref(v_text_2136_);
v___x_2743_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2743_, 0, v_text_2136_);
v___x_2744_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2136_, v___x_2741_, v___x_2743_);
lean_dec_ref(v_text_2136_);
return v___x_2744_;
}
else
{
lean_object* v___x_2745_; 
lean_dec(v___x_2741_);
lean_dec_ref(v_text_2136_);
v___x_2745_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2745_;
}
}
v___jp_2652_:
{
if (v___y_2656_ == 0)
{
v___y_2139_ = v___y_2654_;
v___y_2140_ = v___y_2655_;
v___y_2141_ = v___x_2651_;
goto v___jp_2138_;
}
else
{
if (v___y_2653_ == 0)
{
v___y_2139_ = v___y_2654_;
v___y_2140_ = v___y_2655_;
v___y_2141_ = v___x_2235_;
goto v___jp_2138_;
}
else
{
v___y_2139_ = v___y_2654_;
v___y_2140_ = v___y_2655_;
v___y_2141_ = v___x_2651_;
goto v___jp_2138_;
}
}
}
v___jp_2657_:
{
if (v___y_2658_ == 0)
{
v___y_2653_ = v___y_2661_;
v___y_2654_ = v___y_2659_;
v___y_2655_ = v___y_2660_;
v___y_2656_ = v___x_2235_;
goto v___jp_2652_;
}
else
{
v___y_2653_ = v___y_2661_;
v___y_2654_ = v___y_2659_;
v___y_2655_ = v___y_2660_;
v___y_2656_ = v___x_2651_;
goto v___jp_2652_;
}
}
v___jp_2662_:
{
uint32_t v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = 95;
v___x_2668_ = lean_uint32_dec_eq(v___y_2663_, v___x_2667_);
if (v___x_2668_ == 0)
{
uint8_t v___x_2669_; 
v___x_2669_ = l_Lean_isLetterLike(v___y_2663_);
v___y_2658_ = v___y_2664_;
v___y_2659_ = v___y_2665_;
v___y_2660_ = v___y_2666_;
v___y_2661_ = v___x_2669_;
goto v___jp_2657_;
}
else
{
v___y_2658_ = v___y_2664_;
v___y_2659_ = v___y_2665_;
v___y_2660_ = v___y_2666_;
v___y_2661_ = v___x_2668_;
goto v___jp_2657_;
}
}
v___jp_2670_:
{
if (v___y_2675_ == 0)
{
uint32_t v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = 97;
v___x_2677_ = lean_uint32_dec_le(v___x_2676_, v___y_2671_);
if (v___x_2677_ == 0)
{
v___y_2663_ = v___y_2671_;
v___y_2664_ = v___y_2672_;
v___y_2665_ = v___y_2673_;
v___y_2666_ = v___y_2674_;
goto v___jp_2662_;
}
else
{
uint32_t v___x_2678_; uint8_t v___x_2679_; 
v___x_2678_ = 122;
v___x_2679_ = lean_uint32_dec_le(v___y_2671_, v___x_2678_);
if (v___x_2679_ == 0)
{
v___y_2663_ = v___y_2671_;
v___y_2664_ = v___y_2672_;
v___y_2665_ = v___y_2673_;
v___y_2666_ = v___y_2674_;
goto v___jp_2662_;
}
else
{
v___y_2658_ = v___y_2672_;
v___y_2659_ = v___y_2673_;
v___y_2660_ = v___y_2674_;
v___y_2661_ = v___x_2679_;
goto v___jp_2657_;
}
}
}
else
{
v___y_2658_ = v___y_2672_;
v___y_2659_ = v___y_2673_;
v___y_2660_ = v___y_2674_;
v___y_2661_ = v___y_2675_;
goto v___jp_2657_;
}
}
v___jp_2680_:
{
lean_object* v___x_2684_; 
lean_inc_ref(v___y_2682_);
v___x_2684_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2682_);
if (lean_obj_tag(v___x_2684_) == 0)
{
v___y_2658_ = v___y_2683_;
v___y_2659_ = v___y_2681_;
v___y_2660_ = v___y_2682_;
v___y_2661_ = v___x_2651_;
goto v___jp_2657_;
}
else
{
lean_object* v_val_2685_; lean_object* v___x_2686_; 
v_val_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_val_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2686_ = l_String_Slice_Pos_get_x3f(v_val_2685_, v___x_2642_);
lean_dec(v_val_2685_);
if (lean_obj_tag(v___x_2686_) == 0)
{
v___y_2658_ = v___y_2683_;
v___y_2659_ = v___y_2681_;
v___y_2660_ = v___y_2682_;
v___y_2661_ = v___x_2651_;
goto v___jp_2657_;
}
else
{
lean_object* v_val_2687_; uint32_t v___x_2688_; uint32_t v___x_2689_; uint8_t v___x_2690_; 
v_val_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_val_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v___x_2688_ = 65;
v___x_2689_ = lean_unbox_uint32(v_val_2687_);
v___x_2690_ = lean_uint32_dec_le(v___x_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
uint32_t v___x_2691_; 
v___x_2691_ = lean_unbox_uint32(v_val_2687_);
lean_dec(v_val_2687_);
v___y_2671_ = v___x_2691_;
v___y_2672_ = v___y_2683_;
v___y_2673_ = v___y_2681_;
v___y_2674_ = v___y_2682_;
v___y_2675_ = v___x_2690_;
goto v___jp_2670_;
}
else
{
uint32_t v___x_2692_; uint32_t v___x_2693_; uint8_t v___x_2694_; uint32_t v___x_2695_; 
v___x_2692_ = 90;
v___x_2693_ = lean_unbox_uint32(v_val_2687_);
v___x_2694_ = lean_uint32_dec_le(v___x_2693_, v___x_2692_);
v___x_2695_ = lean_unbox_uint32(v_val_2687_);
lean_dec(v_val_2687_);
v___y_2671_ = v___x_2695_;
v___y_2672_ = v___y_2683_;
v___y_2673_ = v___y_2681_;
v___y_2674_ = v___y_2682_;
v___y_2675_ = v___x_2694_;
goto v___jp_2670_;
}
}
}
}
v___jp_2696_:
{
uint32_t v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = 95;
v___x_2701_ = lean_uint32_dec_eq(v___y_2697_, v___x_2700_);
if (v___x_2701_ == 0)
{
uint8_t v___x_2702_; 
v___x_2702_ = l_Lean_isLetterLike(v___y_2697_);
v___y_2681_ = v___y_2698_;
v___y_2682_ = v___y_2699_;
v___y_2683_ = v___x_2702_;
goto v___jp_2680_;
}
else
{
v___y_2681_ = v___y_2698_;
v___y_2682_ = v___y_2699_;
v___y_2683_ = v___x_2701_;
goto v___jp_2680_;
}
}
v___jp_2703_:
{
if (v___y_2707_ == 0)
{
uint32_t v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = 97;
v___x_2709_ = lean_uint32_dec_le(v___x_2708_, v___y_2704_);
if (v___x_2709_ == 0)
{
v___y_2697_ = v___y_2704_;
v___y_2698_ = v___y_2705_;
v___y_2699_ = v___y_2706_;
goto v___jp_2696_;
}
else
{
uint32_t v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = 122;
v___x_2711_ = lean_uint32_dec_le(v___y_2704_, v___x_2710_);
if (v___x_2711_ == 0)
{
v___y_2697_ = v___y_2704_;
v___y_2698_ = v___y_2705_;
v___y_2699_ = v___y_2706_;
goto v___jp_2696_;
}
else
{
v___y_2681_ = v___y_2705_;
v___y_2682_ = v___y_2706_;
v___y_2683_ = v___x_2711_;
goto v___jp_2680_;
}
}
}
else
{
v___y_2681_ = v___y_2705_;
v___y_2682_ = v___y_2706_;
v___y_2683_ = v___y_2707_;
goto v___jp_2680_;
}
}
v___jp_2712_:
{
if (lean_obj_tag(v_x_2137_) == 2)
{
lean_object* v_val_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_val_2714_ = lean_ctor_get(v_x_2137_, 1);
v___x_2715_ = lean_string_utf8_byte_size(v_val_2714_);
lean_inc_ref(v_val_2714_);
v___x_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2716_, 0, v_val_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2642_);
lean_ctor_set(v___x_2716_, 2, v___x_2715_);
v___x_2717_ = l_String_Slice_Pos_get_x3f(v___x_2716_, v___x_2642_);
lean_dec_ref_known(v___x_2716_, 3);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_inc_ref(v_val_2714_);
v___y_2681_ = v___y_2713_;
v___y_2682_ = v_val_2714_;
v___y_2683_ = v___x_2651_;
goto v___jp_2680_;
}
else
{
lean_object* v_val_2718_; uint32_t v___x_2719_; uint32_t v___x_2720_; uint8_t v___x_2721_; 
v_val_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_val_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = 65;
v___x_2720_ = lean_unbox_uint32(v_val_2718_);
v___x_2721_ = lean_uint32_dec_le(v___x_2719_, v___x_2720_);
if (v___x_2721_ == 0)
{
uint32_t v___x_2722_; 
v___x_2722_ = lean_unbox_uint32(v_val_2718_);
lean_dec(v_val_2718_);
lean_inc_ref(v_val_2714_);
v___y_2704_ = v___x_2722_;
v___y_2705_ = v___y_2713_;
v___y_2706_ = v_val_2714_;
v___y_2707_ = v___x_2721_;
goto v___jp_2703_;
}
else
{
uint32_t v___x_2723_; uint32_t v___x_2724_; uint8_t v___x_2725_; uint32_t v___x_2726_; 
v___x_2723_ = 90;
v___x_2724_ = lean_unbox_uint32(v_val_2718_);
v___x_2725_ = lean_uint32_dec_le(v___x_2724_, v___x_2723_);
v___x_2726_ = lean_unbox_uint32(v_val_2718_);
lean_dec(v_val_2718_);
lean_inc_ref(v_val_2714_);
v___y_2704_ = v___x_2726_;
v___y_2705_ = v___y_2713_;
v___y_2706_ = v_val_2714_;
v___y_2707_ = v___x_2725_;
goto v___jp_2703_;
}
}
}
else
{
lean_dec(v_x_2137_);
return v___y_2713_;
}
}
}
else
{
lean_object* v___x_2746_; 
lean_dec(v___x_2648_);
lean_dec(v_x_2137_);
lean_dec_ref(v_text_2136_);
v___x_2746_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2746_;
}
}
else
{
lean_object* v___x_2747_; lean_object* v_tokens_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2747_ = l_Lean_Syntax_getArg(v_x_2137_, v___x_2642_);
lean_dec(v_x_2137_);
v_tokens_2748_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2136_, v___x_2747_);
v___x_2749_ = 2;
v___x_2750_ = lean_unsigned_to_nat(5u);
v___x_2751_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2751_, 0, v___x_2644_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*2, v___x_2749_);
v___x_2752_ = lean_array_push(v_tokens_2748_, v___x_2751_);
return v___x_2752_;
}
}
v___jp_2138_:
{
if (v___y_2141_ == 0)
{
lean_object* v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; 
v___x_2142_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2143_ = 0;
v___x_2144_ = lean_box(v___x_2143_);
v___x_2145_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2142_, v___y_2140_, v___x_2144_);
lean_dec(v___x_2144_);
lean_dec_ref(v___y_2140_);
v___x_2146_ = lean_unsigned_to_nat(5u);
v___x_2147_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2147_, 0, v_x_2137_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_unbox(v___x_2145_);
lean_dec(v___x_2145_);
lean_ctor_set_uint8(v___x_2147_, sizeof(void*)*2, v___x_2148_);
v___x_2149_ = lean_array_push(v___y_2139_, v___x_2147_);
return v___x_2149_;
}
else
{
lean_dec_ref(v___y_2140_);
lean_dec(v_x_2137_);
return v___y_2139_;
}
}
v___jp_2150_:
{
if (v___y_2153_ == 0)
{
lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2154_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2155_ = 0;
v___x_2156_ = lean_box(v___x_2155_);
v___x_2157_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2154_, v___y_2151_, v___x_2156_);
lean_dec(v___x_2156_);
lean_dec_ref(v___y_2151_);
v___x_2158_ = lean_unsigned_to_nat(5u);
v___x_2159_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2159_, 0, v_x_2137_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_unbox(v___x_2157_);
lean_dec(v___x_2157_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*2, v___x_2160_);
v___x_2161_ = lean_array_push(v___y_2152_, v___x_2159_);
return v___x_2161_;
}
else
{
lean_dec_ref(v___y_2151_);
lean_dec(v_x_2137_);
return v___y_2152_;
}
}
v___jp_2162_:
{
if (v___y_2165_ == 0)
{
lean_object* v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2166_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2167_ = 0;
v___x_2168_ = lean_box(v___x_2167_);
v___x_2169_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2166_, v___y_2164_, v___x_2168_);
lean_dec(v___x_2168_);
lean_dec_ref(v___y_2164_);
v___x_2170_ = lean_unsigned_to_nat(5u);
v___x_2171_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2171_, 0, v_x_2137_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_unbox(v___x_2169_);
lean_dec(v___x_2169_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*2, v___x_2172_);
v___x_2173_ = lean_array_push(v___y_2163_, v___x_2171_);
return v___x_2173_;
}
else
{
lean_dec_ref(v___y_2164_);
lean_dec(v_x_2137_);
return v___y_2163_;
}
}
v___jp_2174_:
{
if (v___y_2177_ == 0)
{
lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; 
v___x_2178_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2179_ = 0;
v___x_2180_ = lean_box(v___x_2179_);
v___x_2181_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2178_, v___y_2176_, v___x_2180_);
lean_dec(v___x_2180_);
lean_dec_ref(v___y_2176_);
v___x_2182_ = lean_unsigned_to_nat(5u);
v___x_2183_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2183_, 0, v_x_2137_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_unbox(v___x_2181_);
lean_dec(v___x_2181_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*2, v___x_2184_);
v___x_2185_ = lean_array_push(v___y_2175_, v___x_2183_);
return v___x_2185_;
}
else
{
lean_dec_ref(v___y_2176_);
lean_dec(v_x_2137_);
return v___y_2175_;
}
}
v___jp_2186_:
{
if (v___y_2192_ == 0)
{
v___y_2175_ = v___y_2187_;
v___y_2176_ = v___y_2191_;
v___y_2177_ = v___y_2188_;
goto v___jp_2174_;
}
else
{
if (v___y_2190_ == 0)
{
v___y_2175_ = v___y_2187_;
v___y_2176_ = v___y_2191_;
v___y_2177_ = v___y_2189_;
goto v___jp_2174_;
}
else
{
v___y_2175_ = v___y_2187_;
v___y_2176_ = v___y_2191_;
v___y_2177_ = v___y_2188_;
goto v___jp_2174_;
}
}
}
v___jp_2193_:
{
if (v___y_2194_ == 0)
{
v___y_2187_ = v___y_2195_;
v___y_2188_ = v___y_2196_;
v___y_2189_ = v___y_2197_;
v___y_2190_ = v___y_2199_;
v___y_2191_ = v___y_2198_;
v___y_2192_ = v___y_2197_;
goto v___jp_2186_;
}
else
{
v___y_2187_ = v___y_2195_;
v___y_2188_ = v___y_2196_;
v___y_2189_ = v___y_2197_;
v___y_2190_ = v___y_2199_;
v___y_2191_ = v___y_2198_;
v___y_2192_ = v___y_2196_;
goto v___jp_2186_;
}
}
v___jp_2200_:
{
uint32_t v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = 95;
v___x_2208_ = lean_uint32_dec_eq(v___y_2205_, v___x_2207_);
if (v___x_2208_ == 0)
{
uint8_t v___x_2209_; 
v___x_2209_ = l_Lean_isLetterLike(v___y_2205_);
v___y_2194_ = v___y_2202_;
v___y_2195_ = v___y_2201_;
v___y_2196_ = v___y_2203_;
v___y_2197_ = v___y_2204_;
v___y_2198_ = v___y_2206_;
v___y_2199_ = v___x_2209_;
goto v___jp_2193_;
}
else
{
v___y_2194_ = v___y_2202_;
v___y_2195_ = v___y_2201_;
v___y_2196_ = v___y_2203_;
v___y_2197_ = v___y_2204_;
v___y_2198_ = v___y_2206_;
v___y_2199_ = v___x_2208_;
goto v___jp_2193_;
}
}
v___jp_2210_:
{
if (v___y_2217_ == 0)
{
uint32_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = 97;
v___x_2219_ = lean_uint32_dec_le(v___x_2218_, v___y_2215_);
if (v___x_2219_ == 0)
{
v___y_2201_ = v___y_2212_;
v___y_2202_ = v___y_2211_;
v___y_2203_ = v___y_2213_;
v___y_2204_ = v___y_2214_;
v___y_2205_ = v___y_2215_;
v___y_2206_ = v___y_2216_;
goto v___jp_2200_;
}
else
{
uint32_t v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = 122;
v___x_2221_ = lean_uint32_dec_le(v___y_2215_, v___x_2220_);
if (v___x_2221_ == 0)
{
v___y_2201_ = v___y_2212_;
v___y_2202_ = v___y_2211_;
v___y_2203_ = v___y_2213_;
v___y_2204_ = v___y_2214_;
v___y_2205_ = v___y_2215_;
v___y_2206_ = v___y_2216_;
goto v___jp_2200_;
}
else
{
v___y_2194_ = v___y_2211_;
v___y_2195_ = v___y_2212_;
v___y_2196_ = v___y_2213_;
v___y_2197_ = v___y_2214_;
v___y_2198_ = v___y_2216_;
v___y_2199_ = v___x_2221_;
goto v___jp_2193_;
}
}
}
else
{
v___y_2194_ = v___y_2211_;
v___y_2195_ = v___y_2212_;
v___y_2196_ = v___y_2213_;
v___y_2197_ = v___y_2214_;
v___y_2198_ = v___y_2216_;
v___y_2199_ = v___y_2217_;
goto v___jp_2193_;
}
}
v___jp_2222_:
{
if (v___y_2225_ == 0)
{
lean_object* v___x_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2226_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2227_ = 0;
v___x_2228_ = lean_box(v___x_2227_);
v___x_2229_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2226_, v___y_2223_, v___x_2228_);
lean_dec(v___x_2228_);
lean_dec_ref(v___y_2223_);
v___x_2230_ = lean_unsigned_to_nat(5u);
v___x_2231_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2231_, 0, v_x_2137_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = lean_unbox(v___x_2229_);
lean_dec(v___x_2229_);
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*2, v___x_2232_);
v___x_2233_ = lean_array_push(v___y_2224_, v___x_2231_);
return v___x_2233_;
}
else
{
lean_dec_ref(v___y_2223_);
lean_dec(v_x_2137_);
return v___y_2224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_2753_, size_t v_sz_2754_, size_t v_i_2755_, lean_object* v_bs_2756_){
_start:
{
uint8_t v___x_2757_; 
v___x_2757_ = lean_usize_dec_lt(v_i_2755_, v_sz_2754_);
if (v___x_2757_ == 0)
{
lean_dec_ref(v_text_2753_);
return v_bs_2756_;
}
else
{
lean_object* v_v_2758_; lean_object* v___x_2759_; lean_object* v_bs_x27_2760_; lean_object* v___x_2761_; size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v_v_2758_ = lean_array_uget(v_bs_2756_, v_i_2755_);
v___x_2759_ = lean_unsigned_to_nat(0u);
v_bs_x27_2760_ = lean_array_uset(v_bs_2756_, v_i_2755_, v___x_2759_);
lean_inc_ref(v_text_2753_);
v___x_2761_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2753_, v_v_2758_);
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_add(v_i_2755_, v___x_2762_);
v___x_2764_ = lean_array_uset(v_bs_x27_2760_, v_i_2755_, v___x_2761_);
v_i_2755_ = v___x_2763_;
v_bs_2756_ = v___x_2764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_2766_, lean_object* v_sz_2767_, lean_object* v_i_2768_, lean_object* v_bs_2769_){
_start:
{
size_t v_sz_boxed_2770_; size_t v_i_boxed_2771_; lean_object* v_res_2772_; 
v_sz_boxed_2770_ = lean_unbox_usize(v_sz_2767_);
lean_dec(v_sz_2767_);
v_i_boxed_2771_ = lean_unbox_usize(v_i_2768_);
lean_dec(v_i_2768_);
v_res_2772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2766_, v_sz_boxed_2770_, v_i_boxed_2771_, v_bs_2769_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_2773_, lean_object* v_t_2774_, lean_object* v_k_2775_, lean_object* v_fallback_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2774_, v_k_2775_, v_fallback_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_2778_, lean_object* v_t_2779_, lean_object* v_k_2780_, lean_object* v_fallback_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_2778_, v_t_2779_, v_k_2780_, v_fallback_2781_);
lean_dec(v_fallback_2781_);
lean_dec_ref(v_k_2780_);
lean_dec(v_t_2779_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_2783_, lean_object* v_info_2784_, lean_object* v_x_2785_){
_start:
{
if (lean_obj_tag(v_info_2784_) == 1)
{
lean_object* v_i_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2830_; 
v_i_2786_ = lean_ctor_get(v_info_2784_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_info_2784_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2788_ = v_info_2784_;
v_isShared_2789_ = v_isSharedCheck_2830_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_i_2786_);
lean_dec(v_info_2784_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2830_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v_toElabInfo_2790_; lean_object* v_lctx_2791_; lean_object* v_expr_2792_; uint8_t v_isBinder_2793_; lean_object* v_stx_2794_; lean_object* v___x_2811_; 
v_toElabInfo_2790_ = lean_ctor_get(v_i_2786_, 0);
lean_inc_ref(v_toElabInfo_2790_);
v_lctx_2791_ = lean_ctor_get(v_i_2786_, 1);
lean_inc_ref(v_lctx_2791_);
v_expr_2792_ = lean_ctor_get(v_i_2786_, 3);
lean_inc_ref(v_expr_2792_);
v_isBinder_2793_ = lean_ctor_get_uint8(v_i_2786_, sizeof(void*)*4);
lean_dec_ref(v_i_2786_);
v_stx_2794_ = lean_ctor_get(v_toElabInfo_2790_, 1);
lean_inc(v_stx_2794_);
lean_dec_ref(v_toElabInfo_2790_);
v___x_2811_ = l_Lean_Syntax_getHeadInfo(v_stx_2794_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
lean_dec_ref_known(v___x_2811_, 4);
v___x_2812_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v_stx_2794_);
v___x_2813_ = l_Lean_Syntax_isOfKind(v_stx_2794_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_dec_ref(v_expr_2792_);
lean_dec_ref(v_lctx_2791_);
lean_del_object(v___x_2788_);
goto v___jp_2802_;
}
else
{
if (lean_obj_tag(v_expr_2792_) == 1)
{
lean_object* v_fvarId_2814_; lean_object* v___x_2815_; 
v_fvarId_2814_ = lean_ctor_get(v_expr_2792_, 0);
lean_inc(v_fvarId_2814_);
lean_dec_ref_known(v_expr_2792_, 1);
v___x_2815_ = lean_local_ctx_find(v_lctx_2791_, v_fvarId_2814_);
if (lean_obj_tag(v___x_2815_) == 1)
{
lean_object* v_val_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2828_; 
v_val_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2828_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_val_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2828_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
uint8_t v___x_2820_; 
v___x_2820_ = l_Lean_LocalDecl_isAuxDecl(v_val_2816_);
if (v___x_2820_ == 0)
{
uint8_t v___x_2821_; 
lean_del_object(v___x_2818_);
v___x_2821_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2816_);
lean_dec(v_val_2816_);
if (v___x_2821_ == 0)
{
goto v___jp_2795_;
}
else
{
if (v___x_2820_ == 0)
{
lean_del_object(v___x_2788_);
goto v___jp_2802_;
}
else
{
goto v___jp_2795_;
}
}
}
else
{
lean_dec(v_val_2816_);
lean_del_object(v___x_2788_);
if (v_isBinder_2793_ == 0)
{
lean_del_object(v___x_2818_);
goto v___jp_2802_;
}
else
{
uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2822_ = 3;
v___x_2823_ = lean_unsigned_to_nat(5u);
v___x_2824_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2824_, 0, v_stx_2794_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2, v___x_2822_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2824_);
v___x_2826_ = v___x_2818_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
else
{
lean_dec(v___x_2815_);
lean_del_object(v___x_2788_);
goto v___jp_2802_;
}
}
else
{
lean_dec_ref(v_expr_2792_);
lean_dec_ref(v_lctx_2791_);
lean_del_object(v___x_2788_);
goto v___jp_2802_;
}
}
}
else
{
lean_object* v___x_2829_; 
lean_dec(v___x_2811_);
lean_dec(v_stx_2794_);
lean_dec_ref(v_expr_2792_);
lean_dec_ref(v_lctx_2791_);
lean_del_object(v___x_2788_);
v___x_2829_ = lean_box(0);
return v___x_2829_;
}
v___jp_2795_:
{
uint8_t v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2796_ = 1;
v___x_2797_ = lean_unsigned_to_nat(5u);
v___x_2798_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2798_, 0, v_stx_2794_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*2, v___x_2796_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v___x_2798_);
v___x_2800_ = v___x_2788_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
v___jp_2802_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
lean_inc(v_stx_2794_);
v___x_2803_ = l_Lean_Syntax_getKind(v_stx_2794_);
v___x_2804_ = l_Lean_Parser_Term_identProjKind;
v___x_2805_ = lean_name_eq(v___x_2803_, v___x_2804_);
lean_dec(v___x_2803_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
lean_dec(v_stx_2794_);
v___x_2806_ = lean_box(0);
return v___x_2806_;
}
else
{
uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2807_ = 2;
v___x_2808_ = lean_unsigned_to_nat(5u);
v___x_2809_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2809_, 0, v_stx_2794_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*2, v___x_2807_);
v___x_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
return v___x_2810_;
}
}
}
}
else
{
lean_object* v___x_2831_; 
lean_dec_ref(v_info_2784_);
v___x_2831_ = lean_box(0);
return v___x_2831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_2832_, lean_object* v_info_2833_, lean_object* v_x_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_2832_, v_info_2833_, v_x_2834_);
lean_dec_ref(v_x_2834_);
lean_dec_ref(v_x_2832_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_2837_){
_start:
{
lean_object* v___f_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___f_2838_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_2839_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_2838_, v_i_2837_);
v___x_2840_ = lean_array_mk(v___x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_2841_, lean_object* v_y_2842_){
_start:
{
lean_object* v_fst_2843_; lean_object* v_fst_2844_; uint8_t v___x_2845_; 
v_fst_2843_ = lean_ctor_get(v_x_2841_, 0);
v_fst_2844_ = lean_ctor_get(v_y_2842_, 0);
v___x_2845_ = lean_nat_dec_le(v_fst_2843_, v_fst_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_2846_, lean_object* v_y_2847_){
_start:
{
uint8_t v_res_2848_; lean_object* v_r_2849_; 
v_res_2848_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_2846_, v_y_2847_);
lean_dec_ref(v_y_2847_);
lean_dec_ref(v_x_2846_);
v_r_2849_ = lean_box(v_res_2848_);
return v_r_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_2850_, lean_object* v_x_2851_){
_start:
{
if (lean_obj_tag(v_x_2851_) == 0)
{
lean_inc(v_x_2850_);
return v_x_2850_;
}
else
{
lean_object* v_key_2852_; lean_object* v_value_2853_; lean_object* v_tail_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_key_2852_ = lean_ctor_get(v_x_2851_, 0);
v_value_2853_ = lean_ctor_get(v_x_2851_, 1);
v_tail_2854_ = lean_ctor_get(v_x_2851_, 2);
v___x_2855_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2850_, v_tail_2854_);
lean_inc(v_value_2853_);
lean_inc(v_key_2852_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_key_2852_);
lean_ctor_set(v___x_2856_, 1, v_value_2853_);
v___x_2857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2855_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_2858_, lean_object* v_x_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2858_, v_x_2859_);
lean_dec(v_x_2859_);
lean_dec(v_x_2858_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_2861_, size_t v_i_2862_, size_t v_stop_2863_, lean_object* v_b_2864_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = lean_usize_dec_eq(v_i_2862_, v_stop_2863_);
if (v___x_2865_ == 0)
{
size_t v___x_2866_; size_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = ((size_t)1ULL);
v___x_2867_ = lean_usize_sub(v_i_2862_, v___x_2866_);
v___x_2868_ = lean_array_uget_borrowed(v_as_2861_, v___x_2867_);
v___x_2869_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_2864_, v___x_2868_);
lean_dec(v_b_2864_);
v_i_2862_ = v___x_2867_;
v_b_2864_ = v___x_2869_;
goto _start;
}
else
{
return v_b_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_2871_, lean_object* v_i_2872_, lean_object* v_stop_2873_, lean_object* v_b_2874_){
_start:
{
size_t v_i_boxed_2875_; size_t v_stop_boxed_2876_; lean_object* v_res_2877_; 
v_i_boxed_2875_ = lean_unbox_usize(v_i_2872_);
lean_dec(v_i_2872_);
v_stop_boxed_2876_ = lean_unbox_usize(v_stop_2873_);
lean_dec(v_stop_2873_);
v_res_2877_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_2871_, v_i_boxed_2875_, v_stop_boxed_2876_, v_b_2874_);
lean_dec_ref(v_as_2871_);
return v_res_2877_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_2878_, lean_object* v_y_2879_){
_start:
{
lean_object* v_fst_2880_; lean_object* v_fst_2881_; uint8_t v___x_2882_; 
v_fst_2880_ = lean_ctor_get(v_x_2878_, 0);
v_fst_2881_ = lean_ctor_get(v_y_2879_, 0);
v___x_2882_ = lean_nat_dec_le(v_fst_2880_, v_fst_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_2883_, lean_object* v_y_2884_){
_start:
{
uint8_t v_res_2885_; lean_object* v_r_2886_; 
v_res_2885_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_2883_, v_y_2884_);
lean_dec_ref(v_y_2884_);
lean_dec_ref(v_x_2883_);
v_r_2886_ = lean_box(v_res_2885_);
return v_r_2886_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_2890_, lean_object* v_x_2891_){
_start:
{
if (lean_obj_tag(v_x_2891_) == 0)
{
return v_x_2890_;
}
else
{
lean_object* v_head_2892_; lean_object* v_snd_2893_; lean_object* v_snd_2894_; lean_object* v_tail_2895_; lean_object* v_fst_2896_; lean_object* v_fst_2897_; lean_object* v_fst_2898_; lean_object* v_snd_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v_fst_2909_; lean_object* v_snd_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_head_2892_ = lean_ctor_get(v_x_2891_, 0);
lean_inc(v_head_2892_);
v_snd_2893_ = lean_ctor_get(v_head_2892_, 1);
lean_inc(v_snd_2893_);
v_snd_2894_ = lean_ctor_get(v_snd_2893_, 1);
lean_inc(v_snd_2894_);
v_tail_2895_ = lean_ctor_get(v_x_2891_, 1);
lean_inc(v_tail_2895_);
lean_dec_ref_known(v_x_2891_, 2);
v_fst_2896_ = lean_ctor_get(v_head_2892_, 0);
lean_inc(v_fst_2896_);
lean_dec(v_head_2892_);
v_fst_2897_ = lean_ctor_get(v_snd_2893_, 0);
lean_inc(v_fst_2897_);
lean_dec(v_snd_2893_);
v_fst_2898_ = lean_ctor_get(v_snd_2894_, 0);
lean_inc(v_fst_2898_);
v_snd_2899_ = lean_ctor_get(v_snd_2894_, 1);
lean_inc(v_snd_2899_);
lean_dec(v_snd_2894_);
v___x_2900_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2901_ = l_Nat_reprFast(v_fst_2896_);
v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
lean_dec_ref(v___x_2901_);
v___x_2903_ = lean_box(0);
v___x_2904_ = 0;
v___x_2905_ = l_Lean_Syntax_formatStx(v_fst_2898_, v___x_2903_, v___x_2904_);
v___x_2906_ = l_Std_Format_defWidth;
v___x_2907_ = lean_unsigned_to_nat(0u);
v___x_2908_ = l_Std_Format_pretty(v___x_2905_, v___x_2906_, v___x_2907_, v___x_2907_);
v_fst_2909_ = lean_ctor_get(v_snd_2899_, 0);
lean_inc(v_fst_2909_);
v_snd_2910_ = lean_ctor_get(v_snd_2899_, 1);
lean_inc(v_snd_2910_);
lean_dec(v_snd_2899_);
v___x_2911_ = l_Nat_reprFast(v_fst_2897_);
v___x_2912_ = lean_string_append(v___x_2900_, v___x_2911_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2914_ = lean_string_append(v_x_2890_, v___x_2913_);
v___x_2915_ = lean_string_append(v___x_2902_, v___x_2913_);
v___x_2916_ = lean_string_append(v___x_2912_, v___x_2913_);
v___x_2917_ = lean_string_append(v___x_2900_, v___x_2908_);
lean_dec_ref(v___x_2908_);
v___x_2918_ = lean_string_append(v___x_2917_, v___x_2913_);
v___x_2919_ = lean_unsigned_to_nat(80u);
v___x_2920_ = l_Lean_Json_pretty(v_fst_2909_, v___x_2919_);
v___x_2921_ = lean_string_append(v___x_2900_, v___x_2920_);
lean_dec_ref(v___x_2920_);
v___x_2922_ = lean_string_append(v___x_2921_, v___x_2913_);
v___x_2923_ = l_Nat_reprFast(v_snd_2910_);
v___x_2924_ = lean_string_append(v___x_2922_, v___x_2923_);
lean_dec_ref(v___x_2923_);
v___x_2925_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2926_ = lean_string_append(v___x_2924_, v___x_2925_);
v___x_2927_ = lean_string_append(v___x_2918_, v___x_2926_);
lean_dec_ref(v___x_2926_);
v___x_2928_ = lean_string_append(v___x_2927_, v___x_2925_);
v___x_2929_ = lean_string_append(v___x_2916_, v___x_2928_);
lean_dec_ref(v___x_2928_);
v___x_2930_ = lean_string_append(v___x_2929_, v___x_2925_);
v___x_2931_ = lean_string_append(v___x_2915_, v___x_2930_);
lean_dec_ref(v___x_2930_);
v___x_2932_ = lean_string_append(v___x_2931_, v___x_2925_);
v___x_2933_ = lean_string_append(v___x_2914_, v___x_2932_);
lean_dec_ref(v___x_2932_);
v_x_2890_ = v___x_2933_;
v_x_2891_ = v_tail_2895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_2938_){
_start:
{
if (lean_obj_tag(v_x_2938_) == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_2939_;
}
else
{
lean_object* v_tail_2940_; 
v_tail_2940_ = lean_ctor_get(v_x_2938_, 1);
if (lean_obj_tag(v_tail_2940_) == 0)
{
lean_object* v_head_2941_; lean_object* v_snd_2942_; lean_object* v_snd_2943_; lean_object* v_fst_2944_; lean_object* v_fst_2945_; lean_object* v_fst_2946_; lean_object* v_snd_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_fst_2957_; lean_object* v_snd_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_head_2941_ = lean_ctor_get(v_x_2938_, 0);
lean_inc(v_head_2941_);
lean_dec_ref_known(v_x_2938_, 2);
v_snd_2942_ = lean_ctor_get(v_head_2941_, 1);
lean_inc(v_snd_2942_);
v_snd_2943_ = lean_ctor_get(v_snd_2942_, 1);
lean_inc(v_snd_2943_);
v_fst_2944_ = lean_ctor_get(v_head_2941_, 0);
lean_inc(v_fst_2944_);
lean_dec(v_head_2941_);
v_fst_2945_ = lean_ctor_get(v_snd_2942_, 0);
lean_inc(v_fst_2945_);
lean_dec(v_snd_2942_);
v_fst_2946_ = lean_ctor_get(v_snd_2943_, 0);
lean_inc(v_fst_2946_);
v_snd_2947_ = lean_ctor_get(v_snd_2943_, 1);
lean_inc(v_snd_2947_);
lean_dec(v_snd_2943_);
v___x_2948_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2949_ = l_Nat_reprFast(v_fst_2944_);
v___x_2950_ = lean_string_append(v___x_2948_, v___x_2949_);
lean_dec_ref(v___x_2949_);
v___x_2951_ = lean_box(0);
v___x_2952_ = 0;
v___x_2953_ = l_Lean_Syntax_formatStx(v_fst_2946_, v___x_2951_, v___x_2952_);
v___x_2954_ = l_Std_Format_defWidth;
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = l_Std_Format_pretty(v___x_2953_, v___x_2954_, v___x_2955_, v___x_2955_);
v_fst_2957_ = lean_ctor_get(v_snd_2947_, 0);
lean_inc(v_fst_2957_);
v_snd_2958_ = lean_ctor_get(v_snd_2947_, 1);
lean_inc(v_snd_2958_);
lean_dec(v_snd_2947_);
v___x_2959_ = l_Nat_reprFast(v_fst_2945_);
v___x_2960_ = lean_string_append(v___x_2948_, v___x_2959_);
lean_dec_ref(v___x_2959_);
v___x_2961_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2962_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2963_ = lean_string_append(v___x_2950_, v___x_2962_);
v___x_2964_ = lean_string_append(v___x_2960_, v___x_2962_);
v___x_2965_ = lean_string_append(v___x_2948_, v___x_2956_);
lean_dec_ref(v___x_2956_);
v___x_2966_ = lean_string_append(v___x_2965_, v___x_2962_);
v___x_2967_ = lean_unsigned_to_nat(80u);
v___x_2968_ = l_Lean_Json_pretty(v_fst_2957_, v___x_2967_);
v___x_2969_ = lean_string_append(v___x_2948_, v___x_2968_);
lean_dec_ref(v___x_2968_);
v___x_2970_ = lean_string_append(v___x_2969_, v___x_2962_);
v___x_2971_ = l_Nat_reprFast(v_snd_2958_);
v___x_2972_ = lean_string_append(v___x_2970_, v___x_2971_);
lean_dec_ref(v___x_2971_);
v___x_2973_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2974_ = lean_string_append(v___x_2972_, v___x_2973_);
v___x_2975_ = lean_string_append(v___x_2966_, v___x_2974_);
lean_dec_ref(v___x_2974_);
v___x_2976_ = lean_string_append(v___x_2975_, v___x_2973_);
v___x_2977_ = lean_string_append(v___x_2964_, v___x_2976_);
lean_dec_ref(v___x_2976_);
v___x_2978_ = lean_string_append(v___x_2977_, v___x_2973_);
v___x_2979_ = lean_string_append(v___x_2963_, v___x_2978_);
lean_dec_ref(v___x_2978_);
v___x_2980_ = lean_string_append(v___x_2979_, v___x_2973_);
v___x_2981_ = lean_string_append(v___x_2961_, v___x_2980_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_2983_ = lean_string_append(v___x_2981_, v___x_2982_);
return v___x_2983_;
}
else
{
lean_object* v_head_2984_; lean_object* v_snd_2985_; lean_object* v_snd_2986_; lean_object* v_fst_2987_; lean_object* v_fst_2988_; lean_object* v_fst_2989_; lean_object* v_snd_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v_fst_3000_; lean_object* v_snd_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint32_t v___x_3026_; lean_object* v___x_3027_; 
lean_inc(v_tail_2940_);
v_head_2984_ = lean_ctor_get(v_x_2938_, 0);
lean_inc(v_head_2984_);
lean_dec_ref_known(v_x_2938_, 2);
v_snd_2985_ = lean_ctor_get(v_head_2984_, 1);
lean_inc(v_snd_2985_);
v_snd_2986_ = lean_ctor_get(v_snd_2985_, 1);
lean_inc(v_snd_2986_);
v_fst_2987_ = lean_ctor_get(v_head_2984_, 0);
lean_inc(v_fst_2987_);
lean_dec(v_head_2984_);
v_fst_2988_ = lean_ctor_get(v_snd_2985_, 0);
lean_inc(v_fst_2988_);
lean_dec(v_snd_2985_);
v_fst_2989_ = lean_ctor_get(v_snd_2986_, 0);
lean_inc(v_fst_2989_);
v_snd_2990_ = lean_ctor_get(v_snd_2986_, 1);
lean_inc(v_snd_2990_);
lean_dec(v_snd_2986_);
v___x_2991_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2992_ = l_Nat_reprFast(v_fst_2987_);
v___x_2993_ = lean_string_append(v___x_2991_, v___x_2992_);
lean_dec_ref(v___x_2992_);
v___x_2994_ = lean_box(0);
v___x_2995_ = 0;
v___x_2996_ = l_Lean_Syntax_formatStx(v_fst_2989_, v___x_2994_, v___x_2995_);
v___x_2997_ = l_Std_Format_defWidth;
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_2999_ = l_Std_Format_pretty(v___x_2996_, v___x_2997_, v___x_2998_, v___x_2998_);
v_fst_3000_ = lean_ctor_get(v_snd_2990_, 0);
lean_inc(v_fst_3000_);
v_snd_3001_ = lean_ctor_get(v_snd_2990_, 1);
lean_inc(v_snd_3001_);
lean_dec(v_snd_2990_);
v___x_3002_ = l_Nat_reprFast(v_fst_2988_);
v___x_3003_ = lean_string_append(v___x_2991_, v___x_3002_);
lean_dec_ref(v___x_3002_);
v___x_3004_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3005_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3006_ = lean_string_append(v___x_2993_, v___x_3005_);
v___x_3007_ = lean_string_append(v___x_3003_, v___x_3005_);
v___x_3008_ = lean_string_append(v___x_2991_, v___x_2999_);
lean_dec_ref(v___x_2999_);
v___x_3009_ = lean_string_append(v___x_3008_, v___x_3005_);
v___x_3010_ = lean_unsigned_to_nat(80u);
v___x_3011_ = l_Lean_Json_pretty(v_fst_3000_, v___x_3010_);
v___x_3012_ = lean_string_append(v___x_2991_, v___x_3011_);
lean_dec_ref(v___x_3011_);
v___x_3013_ = lean_string_append(v___x_3012_, v___x_3005_);
v___x_3014_ = l_Nat_reprFast(v_snd_3001_);
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
v___x_3018_ = lean_string_append(v___x_3009_, v___x_3017_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = lean_string_append(v___x_3018_, v___x_3016_);
v___x_3020_ = lean_string_append(v___x_3007_, v___x_3019_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = lean_string_append(v___x_3020_, v___x_3016_);
v___x_3022_ = lean_string_append(v___x_3006_, v___x_3021_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = lean_string_append(v___x_3022_, v___x_3016_);
v___x_3024_ = lean_string_append(v___x_3004_, v___x_3023_);
lean_dec_ref(v___x_3023_);
v___x_3025_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3024_, v_tail_2940_);
v___x_3026_ = 93;
v___x_3027_ = lean_string_push(v___x_3025_, v___x_3026_);
return v___x_3027_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
if (lean_obj_tag(v_a_3028_) == 0)
{
lean_object* v___x_3030_; 
v___x_3030_ = l_List_reverse___redArg(v_a_3029_);
return v___x_3030_;
}
else
{
lean_object* v_head_3031_; lean_object* v_snd_3032_; lean_object* v_snd_3033_; lean_object* v_tail_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3066_; 
v_head_3031_ = lean_ctor_get(v_a_3028_, 0);
lean_inc(v_head_3031_);
v_snd_3032_ = lean_ctor_get(v_head_3031_, 1);
lean_inc(v_snd_3032_);
v_snd_3033_ = lean_ctor_get(v_snd_3032_, 1);
lean_inc(v_snd_3033_);
v_tail_3034_ = lean_ctor_get(v_a_3028_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v_a_3028_, 0);
lean_dec(v_unused_3067_);
v___x_3036_ = v_a_3028_;
v_isShared_3037_ = v_isSharedCheck_3066_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_tail_3034_);
lean_dec(v_a_3028_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3066_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v_fst_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3064_; 
v_fst_3038_ = lean_ctor_get(v_head_3031_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_head_3031_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v_head_3031_, 1);
lean_dec(v_unused_3065_);
v___x_3040_ = v_head_3031_;
v_isShared_3041_ = v_isSharedCheck_3064_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_fst_3038_);
lean_dec(v_head_3031_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3064_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_fst_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3062_; 
v_fst_3042_ = lean_ctor_get(v_snd_3032_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_snd_3032_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v_snd_3032_, 1);
lean_dec(v_unused_3063_);
v___x_3044_ = v_snd_3032_;
v_isShared_3045_ = v_isSharedCheck_3062_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_fst_3042_);
lean_dec(v_snd_3032_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3062_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v_stx_3046_; uint8_t v_type_3047_; lean_object* v_priority_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v_stx_3046_ = lean_ctor_get(v_snd_3033_, 0);
lean_inc(v_stx_3046_);
v_type_3047_ = lean_ctor_get_uint8(v_snd_3033_, sizeof(void*)*2);
v_priority_3048_ = lean_ctor_get(v_snd_3033_, 1);
lean_inc(v_priority_3048_);
lean_dec(v_snd_3033_);
v___x_3049_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3047_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v_priority_3048_);
lean_ctor_set(v___x_3044_, 0, v___x_3049_);
v___x_3051_ = v___x_3044_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_priority_3048_);
v___x_3051_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3053_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 1, v___x_3051_);
lean_ctor_set(v___x_3040_, 0, v_stx_3046_);
v___x_3053_ = v___x_3040_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_stx_3046_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v_fst_3042_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v_fst_3038_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 1, v_a_3029_);
lean_ctor_set(v___x_3036_, 0, v___x_3055_);
v___x_3057_ = v___x_3036_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_a_3029_);
v___x_3057_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
v_a_3028_ = v_tail_3034_;
v_a_3029_ = v___x_3057_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3070_, lean_object* v_b_3071_){
_start:
{
if (lean_obj_tag(v_as_x27_3070_) == 0)
{
return v_b_3071_;
}
else
{
lean_object* v_head_3072_; lean_object* v_tail_3073_; lean_object* v_fst_3074_; lean_object* v_snd_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_head_3072_ = lean_ctor_get(v_as_x27_3070_, 0);
v_tail_3073_ = lean_ctor_get(v_as_x27_3070_, 1);
v_fst_3074_ = lean_ctor_get(v_head_3072_, 0);
v_snd_3075_ = lean_ctor_get(v_head_3072_, 1);
v___f_3076_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_3075_);
v___x_3077_ = lean_array_to_list(v_snd_3075_);
v___x_3078_ = l_List_mergeSort___redArg(v___x_3077_, v___f_3076_);
lean_inc(v_fst_3074_);
v___x_3079_ = l_Nat_reprFast(v_fst_3074_);
v___x_3080_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3081_ = lean_string_append(v___x_3079_, v___x_3080_);
v___x_3082_ = lean_box(0);
v___x_3083_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3078_, v___x_3082_);
v___x_3084_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3083_);
v___x_3085_ = lean_string_append(v___x_3081_, v___x_3084_);
lean_dec_ref(v___x_3084_);
v___x_3086_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_3087_ = lean_string_append(v___x_3085_, v___x_3086_);
v___x_3088_ = lean_string_append(v_b_3071_, v___x_3087_);
lean_dec_ref(v___x_3087_);
v_as_x27_3070_ = v_tail_3073_;
v_b_3071_ = v___x_3088_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3090_, lean_object* v_b_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3090_, v_b_3091_);
lean_dec(v_as_x27_3090_);
return v_res_3092_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3093_, lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
uint8_t v___x_3095_; 
v___x_3095_ = 0;
return v___x_3095_;
}
else
{
lean_object* v_key_3096_; lean_object* v_tail_3097_; uint8_t v___x_3098_; 
v_key_3096_ = lean_ctor_get(v_x_3094_, 0);
v_tail_3097_ = lean_ctor_get(v_x_3094_, 2);
v___x_3098_ = lean_nat_dec_eq(v_key_3096_, v_a_3093_);
if (v___x_3098_ == 0)
{
v_x_3094_ = v_tail_3097_;
goto _start;
}
else
{
return v___x_3098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3100_, lean_object* v_x_3101_){
_start:
{
uint8_t v_res_3102_; lean_object* v_r_3103_; 
v_res_3102_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3100_, v_x_3101_);
lean_dec(v_x_3101_);
lean_dec(v_a_3100_);
v_r_3103_ = lean_box(v_res_3102_);
return v_r_3103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3104_, lean_object* v_x_3105_){
_start:
{
if (lean_obj_tag(v_x_3105_) == 0)
{
return v_x_3104_;
}
else
{
lean_object* v_key_3106_; lean_object* v_value_3107_; lean_object* v_tail_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3131_; 
v_key_3106_ = lean_ctor_get(v_x_3105_, 0);
v_value_3107_ = lean_ctor_get(v_x_3105_, 1);
v_tail_3108_ = lean_ctor_get(v_x_3105_, 2);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_x_3105_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3110_ = v_x_3105_;
v_isShared_3111_ = v_isSharedCheck_3131_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_tail_3108_);
lean_inc(v_value_3107_);
lean_inc(v_key_3106_);
lean_dec(v_x_3105_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3131_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; uint64_t v___x_3113_; uint64_t v___x_3114_; uint64_t v___x_3115_; uint64_t v_fold_3116_; uint64_t v___x_3117_; uint64_t v___x_3118_; uint64_t v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; size_t v___x_3122_; size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3112_ = lean_array_get_size(v_x_3104_);
v___x_3113_ = lean_uint64_of_nat(v_key_3106_);
v___x_3114_ = 32ULL;
v___x_3115_ = lean_uint64_shift_right(v___x_3113_, v___x_3114_);
v_fold_3116_ = lean_uint64_xor(v___x_3113_, v___x_3115_);
v___x_3117_ = 16ULL;
v___x_3118_ = lean_uint64_shift_right(v_fold_3116_, v___x_3117_);
v___x_3119_ = lean_uint64_xor(v_fold_3116_, v___x_3118_);
v___x_3120_ = lean_uint64_to_usize(v___x_3119_);
v___x_3121_ = lean_usize_of_nat(v___x_3112_);
v___x_3122_ = ((size_t)1ULL);
v___x_3123_ = lean_usize_sub(v___x_3121_, v___x_3122_);
v___x_3124_ = lean_usize_land(v___x_3120_, v___x_3123_);
v___x_3125_ = lean_array_uget_borrowed(v_x_3104_, v___x_3124_);
lean_inc(v___x_3125_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 2, v___x_3125_);
v___x_3127_ = v___x_3110_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_key_3106_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_value_3107_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_array_uset(v_x_3104_, v___x_3124_, v___x_3127_);
v_x_3104_ = v___x_3128_;
v_x_3105_ = v_tail_3108_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3132_, lean_object* v_source_3133_, lean_object* v_target_3134_){
_start:
{
lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3135_ = lean_array_get_size(v_source_3133_);
v___x_3136_ = lean_nat_dec_lt(v_i_3132_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_dec_ref(v_source_3133_);
lean_dec(v_i_3132_);
return v_target_3134_;
}
else
{
lean_object* v_es_3137_; lean_object* v___x_3138_; lean_object* v_source_3139_; lean_object* v_target_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_es_3137_ = lean_array_fget(v_source_3133_, v_i_3132_);
v___x_3138_ = lean_box(0);
v_source_3139_ = lean_array_fset(v_source_3133_, v_i_3132_, v___x_3138_);
v_target_3140_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3134_, v_es_3137_);
v___x_3141_ = lean_unsigned_to_nat(1u);
v___x_3142_ = lean_nat_add(v_i_3132_, v___x_3141_);
lean_dec(v_i_3132_);
v_i_3132_ = v___x_3142_;
v_source_3133_ = v_source_3139_;
v_target_3134_ = v_target_3140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3144_){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v_nbuckets_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3145_ = lean_array_get_size(v_data_3144_);
v___x_3146_ = lean_unsigned_to_nat(2u);
v_nbuckets_3147_ = lean_nat_mul(v___x_3145_, v___x_3146_);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_mk_array(v_nbuckets_3147_, v___x_3149_);
v___x_3151_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3148_, v_data_3144_, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3154_, lean_object* v_a_3155_, lean_object* v_character_3156_, lean_object* v_x_x3f_3157_){
_start:
{
lean_object* v___y_3159_; 
if (lean_obj_tag(v_x_x3f_3157_) == 0)
{
lean_object* v___x_3164_; 
v___x_3164_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3159_ = v___x_3164_;
goto v___jp_3158_;
}
else
{
lean_object* v_val_3165_; 
v_val_3165_ = lean_ctor_get(v_x_x3f_3157_, 0);
lean_inc(v_val_3165_);
lean_dec_ref_known(v_x_x3f_3157_, 1);
v___y_3159_ = v_val_3165_;
goto v___jp_3158_;
}
v___jp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v_character_3154_);
lean_ctor_set(v___x_3160_, 1, v_a_3155_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v_character_3156_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_array_push(v___y_3159_, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3166_, lean_object* v_a_3167_, lean_object* v_character_3168_, lean_object* v_a_3169_, lean_object* v_x_3170_){
_start:
{
if (lean_obj_tag(v_x_3170_) == 0)
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v_val_3173_; lean_object* v___x_3174_; 
v___x_3171_ = lean_box(0);
v___x_3172_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3166_, v_a_3167_, v_character_3168_, v___x_3171_);
v_val_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_val_3173_);
lean_dec(v___x_3172_);
v___x_3174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3174_, 0, v_a_3169_);
lean_ctor_set(v___x_3174_, 1, v_val_3173_);
lean_ctor_set(v___x_3174_, 2, v_x_3170_);
return v___x_3174_;
}
else
{
lean_object* v_key_3175_; lean_object* v_value_3176_; lean_object* v_tail_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3192_; 
v_key_3175_ = lean_ctor_get(v_x_3170_, 0);
v_value_3176_ = lean_ctor_get(v_x_3170_, 1);
v_tail_3177_ = lean_ctor_get(v_x_3170_, 2);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_x_3170_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3179_ = v_x_3170_;
v_isShared_3180_ = v_isSharedCheck_3192_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_tail_3177_);
lean_inc(v_value_3176_);
lean_inc(v_key_3175_);
lean_dec(v_x_3170_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3192_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_nat_dec_eq(v_key_3175_, v_a_3169_);
if (v___x_3181_ == 0)
{
lean_object* v_tail_3182_; lean_object* v___x_3184_; 
v_tail_3182_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3166_, v_a_3167_, v_character_3168_, v_a_3169_, v_tail_3177_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 2, v_tail_3182_);
v___x_3184_ = v___x_3179_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_key_3175_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_value_3176_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_tail_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v_val_3188_; lean_object* v___x_3190_; 
lean_dec(v_key_3175_);
v___x_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3186_, 0, v_value_3176_);
v___x_3187_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3166_, v_a_3167_, v_character_3168_, v___x_3186_);
v_val_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_val_3188_);
lean_dec(v___x_3187_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v_val_3188_);
lean_ctor_set(v___x_3179_, 0, v_a_3169_);
v___x_3190_ = v___x_3179_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3169_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_val_3188_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_tail_3177_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3193_, lean_object* v_a_3194_, lean_object* v_character_3195_, lean_object* v_m_3196_, lean_object* v_a_3197_){
_start:
{
lean_object* v_size_3198_; lean_object* v_buckets_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3251_; 
v_size_3198_ = lean_ctor_get(v_m_3196_, 0);
v_buckets_3199_ = lean_ctor_get(v_m_3196_, 1);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_m_3196_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3201_ = v_m_3196_;
v_isShared_3202_ = v_isSharedCheck_3251_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_buckets_3199_);
lean_inc(v_size_3198_);
lean_dec(v_m_3196_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3251_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; uint64_t v___x_3204_; uint64_t v___x_3205_; uint64_t v___x_3206_; uint64_t v_fold_3207_; uint64_t v___x_3208_; uint64_t v___x_3209_; uint64_t v___x_3210_; size_t v___x_3211_; size_t v___x_3212_; size_t v___x_3213_; size_t v___x_3214_; size_t v___x_3215_; lean_object* v_bkt_3216_; uint8_t v___x_3217_; 
v___x_3203_ = lean_array_get_size(v_buckets_3199_);
v___x_3204_ = lean_uint64_of_nat(v_a_3197_);
v___x_3205_ = 32ULL;
v___x_3206_ = lean_uint64_shift_right(v___x_3204_, v___x_3205_);
v_fold_3207_ = lean_uint64_xor(v___x_3204_, v___x_3206_);
v___x_3208_ = 16ULL;
v___x_3209_ = lean_uint64_shift_right(v_fold_3207_, v___x_3208_);
v___x_3210_ = lean_uint64_xor(v_fold_3207_, v___x_3209_);
v___x_3211_ = lean_uint64_to_usize(v___x_3210_);
v___x_3212_ = lean_usize_of_nat(v___x_3203_);
v___x_3213_ = ((size_t)1ULL);
v___x_3214_ = lean_usize_sub(v___x_3212_, v___x_3213_);
v___x_3215_ = lean_usize_land(v___x_3211_, v___x_3214_);
v_bkt_3216_ = lean_array_uget_borrowed(v_buckets_3199_, v___x_3215_);
v___x_3217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3197_, v_bkt_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v_size_x27_3223_; lean_object* v___x_3224_; lean_object* v_buckets_x27_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3218_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_character_3193_);
lean_ctor_set(v___x_3219_, 1, v_a_3194_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_character_3195_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_array_push(v___x_3218_, v___x_3220_);
v___x_3222_ = lean_unsigned_to_nat(1u);
v_size_x27_3223_ = lean_nat_add(v_size_3198_, v___x_3222_);
lean_dec(v_size_3198_);
lean_inc(v_bkt_3216_);
v___x_3224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3224_, 0, v_a_3197_);
lean_ctor_set(v___x_3224_, 1, v___x_3221_);
lean_ctor_set(v___x_3224_, 2, v_bkt_3216_);
v_buckets_x27_3225_ = lean_array_uset(v_buckets_3199_, v___x_3215_, v___x_3224_);
v___x_3226_ = lean_unsigned_to_nat(4u);
v___x_3227_ = lean_nat_mul(v_size_x27_3223_, v___x_3226_);
v___x_3228_ = lean_unsigned_to_nat(3u);
v___x_3229_ = lean_nat_div(v___x_3227_, v___x_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_array_get_size(v_buckets_x27_3225_);
v___x_3231_ = lean_nat_dec_le(v___x_3229_, v___x_3230_);
lean_dec(v___x_3229_);
if (v___x_3231_ == 0)
{
lean_object* v_val_3232_; lean_object* v___x_3234_; 
v_val_3232_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3225_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v_val_3232_);
lean_ctor_set(v___x_3201_, 0, v_size_x27_3223_);
v___x_3234_ = v___x_3201_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_size_x27_3223_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_val_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
else
{
lean_object* v___x_3237_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v_buckets_x27_3225_);
lean_ctor_set(v___x_3201_, 0, v_size_x27_3223_);
v___x_3237_ = v___x_3201_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_size_x27_3223_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_buckets_x27_3225_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
else
{
lean_object* v___x_3239_; lean_object* v_buckets_x27_3240_; lean_object* v_bkt_x27_3241_; lean_object* v___y_3243_; uint8_t v___x_3248_; 
lean_inc(v_bkt_3216_);
v___x_3239_ = lean_box(0);
v_buckets_x27_3240_ = lean_array_uset(v_buckets_3199_, v___x_3215_, v___x_3239_);
lean_inc(v_a_3197_);
v_bkt_x27_3241_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3193_, v_a_3194_, v_character_3195_, v_a_3197_, v_bkt_3216_);
v___x_3248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3197_, v_bkt_x27_3241_);
lean_dec(v_a_3197_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_unsigned_to_nat(1u);
v___x_3250_ = lean_nat_sub(v_size_3198_, v___x_3249_);
lean_dec(v_size_3198_);
v___y_3243_ = v___x_3250_;
goto v___jp_3242_;
}
else
{
v___y_3243_ = v_size_3198_;
goto v___jp_3242_;
}
v___jp_3242_:
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3244_ = lean_array_uset(v_buckets_x27_3240_, v___x_3215_, v_bkt_x27_3241_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v___x_3244_);
lean_ctor_set(v___x_3201_, 0, v___y_3243_);
v___x_3246_ = v___x_3201_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___y_3243_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3252_, lean_object* v_as_3253_, size_t v_sz_3254_, size_t v_i_3255_, lean_object* v_b_3256_){
_start:
{
lean_object* v_a_3258_; uint8_t v___x_3262_; 
v___x_3262_ = lean_usize_dec_lt(v_i_3255_, v_sz_3254_);
if (v___x_3262_ == 0)
{
lean_dec_ref(v_text_3252_);
return v_b_3256_;
}
else
{
lean_object* v_a_3263_; lean_object* v_stx_3264_; uint8_t v___x_3265_; lean_object* v___x_3266_; 
v_a_3263_ = lean_array_uget_borrowed(v_as_3253_, v_i_3255_);
v_stx_3264_ = lean_ctor_get(v_a_3263_, 0);
v___x_3265_ = 0;
lean_inc_ref(v_text_3252_);
v___x_3266_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3252_, v_stx_3264_, v___x_3265_);
if (lean_obj_tag(v___x_3266_) == 1)
{
lean_object* v_val_3267_; lean_object* v_start_3268_; lean_object* v_end_3269_; lean_object* v_line_3270_; lean_object* v_character_3271_; lean_object* v_character_3272_; lean_object* v___x_3273_; 
v_val_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_val_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v_start_3268_ = lean_ctor_get(v_val_3267_, 0);
lean_inc_ref(v_start_3268_);
v_end_3269_ = lean_ctor_get(v_val_3267_, 1);
lean_inc_ref(v_end_3269_);
lean_dec(v_val_3267_);
v_line_3270_ = lean_ctor_get(v_start_3268_, 0);
lean_inc(v_line_3270_);
v_character_3271_ = lean_ctor_get(v_start_3268_, 1);
lean_inc(v_character_3271_);
lean_dec_ref(v_start_3268_);
v_character_3272_ = lean_ctor_get(v_end_3269_, 1);
lean_inc(v_character_3272_);
lean_dec_ref(v_end_3269_);
lean_inc(v_a_3263_);
v___x_3273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3272_, v_a_3263_, v_character_3271_, v_b_3256_, v_line_3270_);
v_a_3258_ = v___x_3273_;
goto v___jp_3257_;
}
else
{
lean_dec(v___x_3266_);
v_a_3258_ = v_b_3256_;
goto v___jp_3257_;
}
}
v___jp_3257_:
{
size_t v___x_3259_; size_t v___x_3260_; 
v___x_3259_ = ((size_t)1ULL);
v___x_3260_ = lean_usize_add(v_i_3255_, v___x_3259_);
v_i_3255_ = v___x_3260_;
v_b_3256_ = v_a_3258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3274_, lean_object* v_as_3275_, lean_object* v_sz_3276_, lean_object* v_i_3277_, lean_object* v_b_3278_){
_start:
{
size_t v_sz_boxed_3279_; size_t v_i_boxed_3280_; lean_object* v_res_3281_; 
v_sz_boxed_3279_ = lean_unbox_usize(v_sz_3276_);
lean_dec(v_sz_3276_);
v_i_boxed_3280_ = lean_unbox_usize(v_i_3277_);
lean_dec(v_i_3277_);
v_res_3281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3274_, v_as_3275_, v_sz_boxed_3279_, v_i_boxed_3280_, v_b_3278_);
lean_dec_ref(v_as_3275_);
return v_res_3281_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = lean_box(0);
v___x_3283_ = lean_unsigned_to_nat(16u);
v___x_3284_ = lean_mk_array(v___x_3283_, v___x_3282_);
return v___x_3284_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v_byLine_3287_; 
v___x_3285_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3286_ = lean_unsigned_to_nat(0u);
v_byLine_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3287_, 0, v___x_3286_);
lean_ctor_set(v_byLine_3287_, 1, v___x_3285_);
return v_byLine_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3290_, lean_object* v_toks_3291_){
_start:
{
lean_object* v___x_3292_; lean_object* v_byLine_3293_; size_t v_sz_3294_; size_t v___x_3295_; lean_object* v___x_3296_; lean_object* v_buckets_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; lean_object* v___y_3301_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
v___x_3292_ = lean_unsigned_to_nat(0u);
v_byLine_3293_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3294_ = lean_array_size(v_toks_3291_);
v___x_3295_ = ((size_t)0ULL);
v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3290_, v_toks_3291_, v_sz_3294_, v___x_3295_, v_byLine_3293_);
v_buckets_3297_ = lean_ctor_get(v___x_3296_, 1);
lean_inc_ref(v_buckets_3297_);
lean_dec_ref(v___x_3296_);
v___f_3298_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3299_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_array_get_size(v_buckets_3297_);
v___x_3306_ = lean_nat_dec_lt(v___x_3292_, v___x_3305_);
if (v___x_3306_ == 0)
{
lean_dec_ref(v_buckets_3297_);
v___y_3301_ = v___x_3304_;
goto v___jp_3300_;
}
else
{
size_t v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = lean_usize_of_nat(v___x_3305_);
v___x_3308_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3297_, v___x_3307_, v___x_3295_, v___x_3304_);
lean_dec_ref(v_buckets_3297_);
v___y_3301_ = v___x_3308_;
goto v___jp_3300_;
}
v___jp_3300_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = l_List_mergeSort___redArg(v___y_3301_, v___f_3298_);
v___x_3303_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3302_, v___x_3299_);
lean_dec(v___x_3302_);
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3309_, lean_object* v_toks_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3309_, v_toks_3310_);
lean_dec_ref(v_toks_3310_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3312_, lean_object* v_as_x27_3313_, lean_object* v_b_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3313_, v_b_3314_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3317_, lean_object* v_as_x27_3318_, lean_object* v_b_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3317_, v_as_x27_3318_, v_b_3319_, v_a_3320_);
lean_dec(v_as_x27_3318_);
lean_dec(v_as_3317_);
return v_res_3321_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3322_, lean_object* v_a_3323_, lean_object* v_x_3324_){
_start:
{
uint8_t v___x_3325_; 
v___x_3325_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3323_, v_x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3326_, lean_object* v_a_3327_, lean_object* v_x_3328_){
_start:
{
uint8_t v_res_3329_; lean_object* v_r_3330_; 
v_res_3329_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3326_, v_a_3327_, v_x_3328_);
lean_dec(v_x_3328_);
lean_dec(v_a_3327_);
v_r_3330_ = lean_box(v_res_3329_);
return v_r_3330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3331_, lean_object* v_data_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3334_, lean_object* v_i_3335_, lean_object* v_source_3336_, lean_object* v_target_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3335_, v_source_3336_, v_target_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3340_, v_x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3343_, lean_object* v_doc_3344_, lean_object* v_as_x27_3345_, lean_object* v_b_3346_, lean_object* v___y_3347_){
_start:
{
if (lean_obj_tag(v_as_x27_3345_) == 0)
{
lean_object* v___x_3349_; 
lean_dec_ref(v_doc_3344_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_b_3346_);
return v___x_3349_;
}
else
{
lean_object* v_head_3350_; lean_object* v_tail_3351_; lean_object* v___x_3352_; uint8_t v___x_3353_; 
v_head_3350_ = lean_ctor_get(v_as_x27_3345_, 0);
v_tail_3351_ = lean_ctor_get(v_as_x27_3345_, 1);
v___x_3352_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3350_);
v___x_3353_ = lean_nat_dec_le(v___x_3352_, v_beginPos_3343_);
lean_dec(v___x_3352_);
if (v___x_3353_ == 0)
{
lean_object* v_stx_3354_; lean_object* v___x_3355_; 
v_stx_3354_ = lean_ctor_get(v_head_3350_, 0);
v___x_3355_ = l_Lean_Server_RequestM_checkCancelled(v___y_3347_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_toEditableDocumentCore_3356_; lean_object* v_meta_3357_; lean_object* v_text_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec_ref_known(v___x_3355_, 1);
v_toEditableDocumentCore_3356_ = lean_ctor_get(v_doc_3344_, 0);
v_meta_3357_ = lean_ctor_get(v_toEditableDocumentCore_3356_, 0);
v_text_3358_ = lean_ctor_get(v_meta_3357_, 3);
lean_inc(v_stx_3354_);
lean_inc_ref(v_text_3358_);
v___x_3359_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3358_, v_stx_3354_);
lean_inc(v_head_3350_);
v___x_3360_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3350_);
v___x_3361_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3360_);
v___x_3362_ = l_Array_append___redArg(v_b_3346_, v___x_3359_);
lean_dec_ref(v___x_3359_);
v___x_3363_ = l_Array_append___redArg(v___x_3362_, v___x_3361_);
lean_dec_ref(v___x_3361_);
v_as_x27_3345_ = v_tail_3351_;
v_b_3346_ = v___x_3363_;
goto _start;
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v_b_3346_);
lean_dec_ref(v_doc_3344_);
v_a_3365_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3355_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3355_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
v_as_x27_3345_ = v_tail_3351_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3374_, lean_object* v_doc_3375_, lean_object* v_as_x27_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3374_, v_doc_3375_, v_as_x27_3376_, v_b_3377_, v___y_3378_);
lean_dec_ref(v___y_3378_);
lean_dec(v_as_x27_3376_);
lean_dec(v_beginPos_3374_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3381_, lean_object* v_beginPos_3382_, lean_object* v_endPos_x3f_3383_, lean_object* v_snaps_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_leanSemanticTokens_3387_; lean_object* v___x_3388_; 
v_leanSemanticTokens_3387_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3381_);
v___x_3388_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3382_, v_doc_3381_, v_snaps_3384_, v_leanSemanticTokens_3387_, v_a_3385_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = l_Lean_Server_RequestM_checkCancelled(v_a_3385_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v___x_3391_; 
lean_dec_ref_known(v___x_3390_, 1);
v___x_3391_ = l_Lean_Server_RequestM_checkCancelled(v_a_3385_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3404_; 
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; 
v_unused_3405_ = lean_ctor_get(v___x_3391_, 0);
lean_dec(v_unused_3405_);
v___x_3393_ = v___x_3391_;
v_isShared_3394_ = v_isSharedCheck_3404_;
goto v_resetjp_3392_;
}
else
{
lean_dec(v___x_3391_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3404_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v_toEditableDocumentCore_3395_; lean_object* v_meta_3396_; lean_object* v_text_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v_toEditableDocumentCore_3395_ = lean_ctor_get(v_doc_3381_, 0);
lean_inc_ref(v_toEditableDocumentCore_3395_);
lean_dec_ref(v_doc_3381_);
v_meta_3396_ = lean_ctor_get(v_toEditableDocumentCore_3395_, 0);
lean_inc_ref(v_meta_3396_);
lean_dec_ref(v_toEditableDocumentCore_3395_);
v_text_3397_ = lean_ctor_get(v_meta_3396_, 3);
lean_inc_ref(v_text_3397_);
lean_dec_ref(v_meta_3396_);
v___x_3398_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3397_, v_beginPos_3382_, v_endPos_x3f_3383_, v_a_3389_);
lean_dec(v_a_3389_);
v___x_3399_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3398_);
v___x_3400_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3399_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3400_);
v___x_3402_ = v___x_3393_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v_a_3389_);
lean_dec_ref(v_doc_3381_);
v_a_3406_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3391_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3391_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec(v_a_3389_);
lean_dec_ref(v_doc_3381_);
v_a_3414_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3390_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3390_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec_ref(v_doc_3381_);
v_a_3422_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3388_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3388_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3430_, lean_object* v_beginPos_3431_, lean_object* v_endPos_x3f_3432_, lean_object* v_snaps_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3430_, v_beginPos_3431_, v_endPos_x3f_3432_, v_snaps_3433_, v_a_3434_);
lean_dec_ref(v_a_3434_);
lean_dec(v_snaps_3433_);
lean_dec(v_endPos_x3f_3432_);
lean_dec(v_beginPos_3431_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3437_, lean_object* v_doc_3438_, lean_object* v_as_3439_, lean_object* v_as_x27_3440_, lean_object* v_b_3441_, lean_object* v_a_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3437_, v_doc_3438_, v_as_x27_3440_, v_b_3441_, v___y_3443_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3446_, lean_object* v_doc_3447_, lean_object* v_as_3448_, lean_object* v_as_x27_3449_, lean_object* v_b_3450_, lean_object* v_a_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3446_, v_doc_3447_, v_as_3448_, v_as_x27_3449_, v_b_3450_, v_a_3451_, v___y_3452_);
lean_dec_ref(v___y_3452_);
lean_dec(v_as_x27_3449_);
lean_dec(v_as_3448_);
lean_dec(v_beginPos_3446_);
return v_res_3454_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_box(0);
return v___x_3463_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_box(0);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_3465_){
_start:
{
lean_object* v_doc_3467_; lean_object* v___x_3468_; 
v_doc_3467_ = lean_ctor_get(v___y_3465_, 1);
lean_inc_ref(v_doc_3467_);
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v_doc_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_3469_);
lean_dec_ref(v___y_3469_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_3472_){
_start:
{
lean_object* v___x_3474_; lean_object* v_a_3475_; lean_object* v_toEditableDocumentCore_3476_; lean_object* v_cmdSnaps_3477_; lean_object* v_cancelTk_3478_; uint32_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v_snd_3482_; lean_object* v_fst_3483_; lean_object* v_snd_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3513_; 
v___x_3474_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3472_);
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref(v___x_3474_);
v_toEditableDocumentCore_3476_ = lean_ctor_get(v_a_3475_, 0);
v_cmdSnaps_3477_ = lean_ctor_get(v_toEditableDocumentCore_3476_, 2);
v_cancelTk_3478_ = lean_ctor_get(v_a_3472_, 4);
v___x_3479_ = 3000;
v___x_3480_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_3478_);
lean_inc(v_cmdSnaps_3477_);
v___x_3481_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_3477_, v___x_3479_, v___x_3480_);
v_snd_3482_ = lean_ctor_get(v___x_3481_, 1);
lean_inc(v_snd_3482_);
v_fst_3483_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_fst_3483_);
lean_dec_ref(v___x_3481_);
v_snd_3484_ = lean_ctor_get(v_snd_3482_, 1);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_snd_3482_);
if (v_isSharedCheck_3513_ == 0)
{
lean_object* v_unused_3514_; 
v_unused_3514_ = lean_ctor_get(v_snd_3482_, 0);
lean_dec(v_unused_3514_);
v___x_3486_ = v_snd_3482_;
v_isShared_3487_ = v_isSharedCheck_3513_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_snd_3484_);
lean_dec(v_snd_3482_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3513_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = lean_unsigned_to_nat(0u);
v___x_3489_ = lean_box(0);
v___x_3490_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3475_, v___x_3488_, v___x_3489_, v_fst_3483_, v_a_3472_);
lean_dec(v_fst_3483_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3504_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3504_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3504_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3495_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3495_, 0, v_a_3491_);
v___x_3496_ = lean_unbox(v_snd_3484_);
lean_dec(v_snd_3484_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*1, v___x_3496_);
v___x_3497_ = lean_box(0);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v___x_3497_);
lean_ctor_set(v___x_3486_, 0, v___x_3495_);
v___x_3499_ = v___x_3486_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3501_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3499_);
v___x_3501_ = v___x_3493_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_del_object(v___x_3486_);
lean_dec(v_snd_3484_);
v_a_3505_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3490_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3490_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3515_);
lean_dec_ref(v_a_3515_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_3518_, lean_object* v_x_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3520_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_3523_, lean_object* v_x_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_3523_, v_x_3524_, v_a_3525_);
lean_dec_ref(v_a_3525_);
lean_dec_ref(v_x_3523_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_3528_){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = lean_box(0);
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v_a_3528_);
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3533_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3537_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_3541_, v_a_3542_, v_a_3543_);
lean_dec_ref(v_a_3543_);
lean_dec_ref(v_x_3541_);
return v_res_3545_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_3546_, lean_object* v_x_3547_){
_start:
{
lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3548_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_3547_);
v___x_3549_ = lean_nat_dec_le(v___x_3546_, v___x_3548_);
lean_dec(v___x_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_3550_, lean_object* v_x_3551_){
_start:
{
uint8_t v_res_3552_; lean_object* v_r_3553_; 
v_res_3552_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_3550_, v_x_3551_);
lean_dec_ref(v_x_3551_);
lean_dec(v___x_3550_);
v_r_3553_ = lean_box(v_res_3552_);
return v_r_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_3554_, lean_object* v_a_3555_, lean_object* v___x_3556_, lean_object* v_x_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_fst_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_fst_3560_ = lean_ctor_get(v_x_3557_, 0);
v___x_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3554_);
v___x_3562_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3555_, v___x_3556_, v___x_3561_, v_fst_3560_, v___y_3558_);
lean_dec_ref_known(v___x_3561_, 1);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_3563_, lean_object* v_a_3564_, lean_object* v___x_3565_, lean_object* v_x_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_3563_, v_a_3564_, v___x_3565_, v_x_3566_, v___y_3567_);
lean_dec_ref(v___y_3567_);
lean_dec_ref(v_x_3566_);
lean_dec(v___x_3565_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3573_; lean_object* v_a_3574_; lean_object* v_toEditableDocumentCore_3575_; lean_object* v_meta_3576_; lean_object* v_range_3577_; lean_object* v_cmdSnaps_3578_; lean_object* v_text_3579_; lean_object* v_start_3580_; lean_object* v_end_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3573_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3571_);
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref(v___x_3573_);
v_toEditableDocumentCore_3575_ = lean_ctor_get(v_a_3574_, 0);
v_meta_3576_ = lean_ctor_get(v_toEditableDocumentCore_3575_, 0);
v_range_3577_ = lean_ctor_get(v_p_3570_, 1);
lean_inc_ref(v_range_3577_);
lean_dec_ref(v_p_3570_);
v_cmdSnaps_3578_ = lean_ctor_get(v_toEditableDocumentCore_3575_, 2);
lean_inc(v_cmdSnaps_3578_);
v_text_3579_ = lean_ctor_get(v_meta_3576_, 3);
v_start_3580_ = lean_ctor_get(v_range_3577_, 0);
lean_inc_ref(v_start_3580_);
v_end_3581_ = lean_ctor_get(v_range_3577_, 1);
lean_inc_ref(v_end_3581_);
lean_dec_ref(v_range_3577_);
v___x_3582_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3579_, v_start_3580_);
v___x_3583_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3579_, v_end_3581_);
lean_inc(v___x_3583_);
v___f_3584_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3584_, 0, v___x_3583_);
v___f_3585_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3585_, 0, v___x_3583_);
lean_closure_set(v___f_3585_, 1, v_a_3574_);
lean_closure_set(v___f_3585_, 2, v___x_3582_);
v___x_3586_ = l_Lean_AsyncList_waitUntil___redArg(v___f_3584_, v_cmdSnaps_3578_);
v___x_3587_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3586_, v___f_3585_, v_a_3571_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_3588_, v_a_3589_);
lean_dec_ref(v_a_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_3592_, lean_object* v_i_3593_, lean_object* v_k_3594_){
_start:
{
lean_object* v___x_3595_; uint8_t v___x_3596_; 
v___x_3595_ = lean_array_get_size(v_keys_3592_);
v___x_3596_ = lean_nat_dec_lt(v_i_3593_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_dec(v_i_3593_);
return v___x_3596_;
}
else
{
lean_object* v_k_x27_3597_; uint8_t v___x_3598_; 
v_k_x27_3597_ = lean_array_fget_borrowed(v_keys_3592_, v_i_3593_);
v___x_3598_ = lean_string_dec_eq(v_k_3594_, v_k_x27_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = lean_unsigned_to_nat(1u);
v___x_3600_ = lean_nat_add(v_i_3593_, v___x_3599_);
lean_dec(v_i_3593_);
v_i_3593_ = v___x_3600_;
goto _start;
}
else
{
lean_dec(v_i_3593_);
return v___x_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_3602_, lean_object* v_i_3603_, lean_object* v_k_3604_){
_start:
{
uint8_t v_res_3605_; lean_object* v_r_3606_; 
v_res_3605_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_3602_, v_i_3603_, v_k_3604_);
lean_dec_ref(v_k_3604_);
lean_dec_ref(v_keys_3602_);
v_r_3606_ = lean_box(v_res_3605_);
return v_r_3606_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_3607_, size_t v_x_3608_, lean_object* v_x_3609_){
_start:
{
if (lean_obj_tag(v_x_3607_) == 0)
{
lean_object* v_es_3610_; lean_object* v___x_3611_; size_t v___x_3612_; size_t v___x_3613_; lean_object* v_j_3614_; lean_object* v___x_3615_; 
v_es_3610_ = lean_ctor_get(v_x_3607_, 0);
v___x_3611_ = lean_box(2);
v___x_3612_ = ((size_t)31ULL);
v___x_3613_ = lean_usize_land(v_x_3608_, v___x_3612_);
v_j_3614_ = lean_usize_to_nat(v___x_3613_);
v___x_3615_ = lean_array_get_borrowed(v___x_3611_, v_es_3610_, v_j_3614_);
lean_dec(v_j_3614_);
switch(lean_obj_tag(v___x_3615_))
{
case 0:
{
lean_object* v_key_3616_; uint8_t v___x_3617_; 
v_key_3616_ = lean_ctor_get(v___x_3615_, 0);
v___x_3617_ = lean_string_dec_eq(v_x_3609_, v_key_3616_);
return v___x_3617_;
}
case 1:
{
lean_object* v_node_3618_; size_t v___x_3619_; size_t v___x_3620_; 
v_node_3618_ = lean_ctor_get(v___x_3615_, 0);
v___x_3619_ = ((size_t)5ULL);
v___x_3620_ = lean_usize_shift_right(v_x_3608_, v___x_3619_);
v_x_3607_ = v_node_3618_;
v_x_3608_ = v___x_3620_;
goto _start;
}
default: 
{
uint8_t v___x_3622_; 
v___x_3622_ = 0;
return v___x_3622_;
}
}
}
else
{
lean_object* v_ks_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v_ks_3623_ = lean_ctor_get(v_x_3607_, 0);
v___x_3624_ = lean_unsigned_to_nat(0u);
v___x_3625_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_3623_, v___x_3624_, v_x_3609_);
return v___x_3625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_3626_, lean_object* v_x_3627_, lean_object* v_x_3628_){
_start:
{
size_t v_x_2466__boxed_3629_; uint8_t v_res_3630_; lean_object* v_r_3631_; 
v_x_2466__boxed_3629_ = lean_unbox_usize(v_x_3627_);
lean_dec(v_x_3627_);
v_res_3630_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3626_, v_x_2466__boxed_3629_, v_x_3628_);
lean_dec_ref(v_x_3628_);
lean_dec_ref(v_x_3626_);
v_r_3631_ = lean_box(v_res_3630_);
return v_r_3631_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_3632_, lean_object* v_x_3633_){
_start:
{
uint64_t v___x_3634_; size_t v___x_3635_; uint8_t v___x_3636_; 
v___x_3634_ = lean_string_hash(v_x_3633_);
v___x_3635_ = lean_uint64_to_usize(v___x_3634_);
v___x_3636_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3632_, v___x_3635_, v_x_3633_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
uint8_t v_res_3639_; lean_object* v_r_3640_; 
v_res_3639_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_3637_, v_x_3638_);
lean_dec_ref(v_x_3638_);
lean_dec_ref(v_x_3637_);
v_r_3640_ = lean_box(v_res_3639_);
return v_r_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_3641_, lean_object* v_x_3642_){
_start:
{
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_3643_, v_x_3644_);
lean_dec_ref(v_x_3644_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
lean_object* v_ks_3650_; lean_object* v_vs_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3675_; 
v_ks_3650_ = lean_ctor_get(v_x_3646_, 0);
v_vs_3651_ = lean_ctor_get(v_x_3646_, 1);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_x_3646_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3653_ = v_x_3646_;
v_isShared_3654_ = v_isSharedCheck_3675_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_vs_3651_);
lean_inc(v_ks_3650_);
lean_dec(v_x_3646_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3675_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3655_ = lean_array_get_size(v_ks_3650_);
v___x_3656_ = lean_nat_dec_lt(v_x_3647_, v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_dec(v_x_3647_);
v___x_3657_ = lean_array_push(v_ks_3650_, v_x_3648_);
v___x_3658_ = lean_array_push(v_vs_3651_, v_x_3649_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v___x_3658_);
lean_ctor_set(v___x_3653_, 0, v___x_3657_);
v___x_3660_ = v___x_3653_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
else
{
lean_object* v_k_x27_3662_; uint8_t v___x_3663_; 
v_k_x27_3662_ = lean_array_fget_borrowed(v_ks_3650_, v_x_3647_);
v___x_3663_ = lean_string_dec_eq(v_x_3648_, v_k_x27_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3665_; 
if (v_isShared_3654_ == 0)
{
v___x_3665_ = v___x_3653_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_ks_3650_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_vs_3651_);
v___x_3665_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_unsigned_to_nat(1u);
v___x_3667_ = lean_nat_add(v_x_3647_, v___x_3666_);
lean_dec(v_x_3647_);
v_x_3646_ = v___x_3665_;
v_x_3647_ = v___x_3667_;
goto _start;
}
}
else
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3670_ = lean_array_fset(v_ks_3650_, v_x_3647_, v_x_3648_);
v___x_3671_ = lean_array_fset(v_vs_3651_, v_x_3647_, v_x_3649_);
lean_dec(v_x_3647_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v___x_3671_);
lean_ctor_set(v___x_3653_, 0, v___x_3670_);
v___x_3673_ = v___x_3653_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_3676_, lean_object* v_k_3677_, lean_object* v_v_3678_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_3676_, v___x_3679_, v_k_3677_, v_v_3678_);
return v___x_3680_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_3682_, size_t v_x_3683_, size_t v_x_3684_, lean_object* v_x_3685_, lean_object* v_x_3686_){
_start:
{
if (lean_obj_tag(v_x_3682_) == 0)
{
lean_object* v_es_3687_; size_t v___x_3688_; size_t v___x_3689_; lean_object* v_j_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
v_es_3687_ = lean_ctor_get(v_x_3682_, 0);
v___x_3688_ = ((size_t)31ULL);
v___x_3689_ = lean_usize_land(v_x_3683_, v___x_3688_);
v_j_3690_ = lean_usize_to_nat(v___x_3689_);
v___x_3691_ = lean_array_get_size(v_es_3687_);
v___x_3692_ = lean_nat_dec_lt(v_j_3690_, v___x_3691_);
if (v___x_3692_ == 0)
{
lean_dec(v_j_3690_);
lean_dec(v_x_3686_);
lean_dec_ref(v_x_3685_);
return v_x_3682_;
}
else
{
lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3731_; 
lean_inc_ref(v_es_3687_);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_x_3682_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v_x_3682_, 0);
lean_dec(v_unused_3732_);
v___x_3694_ = v_x_3682_;
v_isShared_3695_ = v_isSharedCheck_3731_;
goto v_resetjp_3693_;
}
else
{
lean_dec(v_x_3682_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3731_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_v_3696_; lean_object* v___x_3697_; lean_object* v_xs_x27_3698_; lean_object* v___y_3700_; 
v_v_3696_ = lean_array_fget(v_es_3687_, v_j_3690_);
v___x_3697_ = lean_box(0);
v_xs_x27_3698_ = lean_array_fset(v_es_3687_, v_j_3690_, v___x_3697_);
switch(lean_obj_tag(v_v_3696_))
{
case 0:
{
lean_object* v_key_3705_; lean_object* v_val_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3716_; 
v_key_3705_ = lean_ctor_get(v_v_3696_, 0);
v_val_3706_ = lean_ctor_get(v_v_3696_, 1);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_v_3696_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3708_ = v_v_3696_;
v_isShared_3709_ = v_isSharedCheck_3716_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_val_3706_);
lean_inc(v_key_3705_);
lean_dec(v_v_3696_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3716_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
uint8_t v___x_3710_; 
v___x_3710_ = lean_string_dec_eq(v_x_3685_, v_key_3705_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_del_object(v___x_3708_);
v___x_3711_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3705_, v_val_3706_, v_x_3685_, v_x_3686_);
v___x_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
v___y_3700_ = v___x_3712_;
goto v___jp_3699_;
}
else
{
lean_object* v___x_3714_; 
lean_dec(v_val_3706_);
lean_dec(v_key_3705_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 1, v_x_3686_);
lean_ctor_set(v___x_3708_, 0, v_x_3685_);
v___x_3714_ = v___x_3708_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_x_3685_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_x_3686_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
v___y_3700_ = v___x_3714_;
goto v___jp_3699_;
}
}
}
}
case 1:
{
lean_object* v_node_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3729_; 
v_node_3717_ = lean_ctor_get(v_v_3696_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_v_3696_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3719_ = v_v_3696_;
v_isShared_3720_ = v_isSharedCheck_3729_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_node_3717_);
lean_dec(v_v_3696_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3729_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
size_t v___x_3721_; size_t v___x_3722_; size_t v___x_3723_; size_t v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3721_ = ((size_t)5ULL);
v___x_3722_ = lean_usize_shift_right(v_x_3683_, v___x_3721_);
v___x_3723_ = ((size_t)1ULL);
v___x_3724_ = lean_usize_add(v_x_3684_, v___x_3723_);
v___x_3725_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_3717_, v___x_3722_, v___x_3724_, v_x_3685_, v_x_3686_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v___x_3725_);
v___x_3727_ = v___x_3719_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
v___y_3700_ = v___x_3727_;
goto v___jp_3699_;
}
}
}
default: 
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_x_3685_);
lean_ctor_set(v___x_3730_, 1, v_x_3686_);
v___y_3700_ = v___x_3730_;
goto v___jp_3699_;
}
}
v___jp_3699_:
{
lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3701_ = lean_array_fset(v_xs_x27_3698_, v_j_3690_, v___y_3700_);
lean_dec(v_j_3690_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3701_);
v___x_3703_ = v___x_3694_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
else
{
lean_object* v_ks_3733_; lean_object* v_vs_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3752_; 
v_ks_3733_ = lean_ctor_get(v_x_3682_, 0);
v_vs_3734_ = lean_ctor_get(v_x_3682_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_x_3682_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3736_ = v_x_3682_;
v_isShared_3737_ = v_isSharedCheck_3752_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_vs_3734_);
lean_inc(v_ks_3733_);
lean_dec(v_x_3682_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3752_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_ks_3733_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_vs_3734_);
v___x_3739_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v_newNode_3740_; size_t v___x_3741_; uint8_t v___x_3742_; 
v_newNode_3740_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_3739_, v_x_3685_, v_x_3686_);
v___x_3741_ = ((size_t)7ULL);
v___x_3742_ = lean_usize_dec_le(v___x_3741_, v_x_3684_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3743_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3740_);
v___x_3744_ = lean_unsigned_to_nat(4u);
v___x_3745_ = lean_nat_dec_lt(v___x_3743_, v___x_3744_);
lean_dec(v___x_3743_);
if (v___x_3745_ == 0)
{
lean_object* v_ks_3746_; lean_object* v_vs_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_ks_3746_ = lean_ctor_get(v_newNode_3740_, 0);
lean_inc_ref(v_ks_3746_);
v_vs_3747_ = lean_ctor_get(v_newNode_3740_, 1);
lean_inc_ref(v_vs_3747_);
lean_dec_ref(v_newNode_3740_);
v___x_3748_ = lean_unsigned_to_nat(0u);
v___x_3749_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_3750_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_3684_, v_ks_3746_, v_vs_3747_, v___x_3748_, v___x_3749_);
lean_dec_ref(v_vs_3747_);
lean_dec_ref(v_ks_3746_);
return v___x_3750_;
}
else
{
return v_newNode_3740_;
}
}
else
{
return v_newNode_3740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_3753_, lean_object* v_keys_3754_, lean_object* v_vals_3755_, lean_object* v_i_3756_, lean_object* v_entries_3757_){
_start:
{
lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3758_ = lean_array_get_size(v_keys_3754_);
v___x_3759_ = lean_nat_dec_lt(v_i_3756_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_dec(v_i_3756_);
return v_entries_3757_;
}
else
{
lean_object* v_k_3760_; lean_object* v_v_3761_; uint64_t v___x_3762_; size_t v_h_3763_; size_t v___x_3764_; lean_object* v___x_3765_; size_t v___x_3766_; size_t v___x_3767_; size_t v___x_3768_; size_t v_h_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_k_3760_ = lean_array_fget_borrowed(v_keys_3754_, v_i_3756_);
v_v_3761_ = lean_array_fget_borrowed(v_vals_3755_, v_i_3756_);
v___x_3762_ = lean_string_hash(v_k_3760_);
v_h_3763_ = lean_uint64_to_usize(v___x_3762_);
v___x_3764_ = ((size_t)5ULL);
v___x_3765_ = lean_unsigned_to_nat(1u);
v___x_3766_ = ((size_t)1ULL);
v___x_3767_ = lean_usize_sub(v_depth_3753_, v___x_3766_);
v___x_3768_ = lean_usize_mul(v___x_3764_, v___x_3767_);
v_h_3769_ = lean_usize_shift_right(v_h_3763_, v___x_3768_);
v___x_3770_ = lean_nat_add(v_i_3756_, v___x_3765_);
lean_dec(v_i_3756_);
lean_inc(v_v_3761_);
lean_inc(v_k_3760_);
v___x_3771_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_3757_, v_h_3769_, v_depth_3753_, v_k_3760_, v_v_3761_);
v_i_3756_ = v___x_3770_;
v_entries_3757_ = v___x_3771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_3773_, lean_object* v_keys_3774_, lean_object* v_vals_3775_, lean_object* v_i_3776_, lean_object* v_entries_3777_){
_start:
{
size_t v_depth_boxed_3778_; lean_object* v_res_3779_; 
v_depth_boxed_3778_ = lean_unbox_usize(v_depth_3773_);
lean_dec(v_depth_3773_);
v_res_3779_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_3778_, v_keys_3774_, v_vals_3775_, v_i_3776_, v_entries_3777_);
lean_dec_ref(v_vals_3775_);
lean_dec_ref(v_keys_3774_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_3780_, lean_object* v_x_3781_, lean_object* v_x_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_){
_start:
{
size_t v_x_2601__boxed_3785_; size_t v_x_2602__boxed_3786_; lean_object* v_res_3787_; 
v_x_2601__boxed_3785_ = lean_unbox_usize(v_x_3781_);
lean_dec(v_x_3781_);
v_x_2602__boxed_3786_ = lean_unbox_usize(v_x_3782_);
lean_dec(v_x_3782_);
v_res_3787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3780_, v_x_2601__boxed_3785_, v_x_2602__boxed_3786_, v_x_3783_, v_x_3784_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_3788_, lean_object* v_x_3789_, lean_object* v_x_3790_){
_start:
{
uint64_t v___x_3791_; size_t v___x_3792_; size_t v___x_3793_; lean_object* v___x_3794_; 
v___x_3791_ = lean_string_hash(v_x_3789_);
v___x_3792_ = lean_uint64_to_usize(v___x_3791_);
v___x_3793_ = ((size_t)1ULL);
v___x_3794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3788_, v___x_3792_, v___x_3793_, v_x_3789_, v_x_3790_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_3796_){
_start:
{
lean_object* v___x_3797_; 
lean_inc(v_params_3796_);
v___x_3797_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_3796_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3813_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3813_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3813_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
uint8_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
v___x_3802_ = 3;
v___x_3803_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_3804_ = l_Lean_Json_compress(v_params_3796_);
v___x_3805_ = lean_string_append(v___x_3803_, v___x_3804_);
lean_dec_ref(v___x_3804_);
v___x_3806_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_3807_ = lean_string_append(v___x_3805_, v___x_3806_);
v___x_3808_ = lean_string_append(v___x_3807_, v_a_3798_);
lean_dec(v_a_3798_);
v___x_3809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
lean_ctor_set_uint8(v___x_3809_, sizeof(void*)*1, v___x_3802_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3809_);
v___x_3811_ = v___x_3800_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_params_3796_);
v_a_3814_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3797_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3797_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_3822_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_3822_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set_tag(v___x_3827_, 1);
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
v_a_3833_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3824_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3824_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 0);
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_3841_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_3844_, lean_object* v_inst_3845_, lean_object* v_handler_3846_, lean_object* v_param_3847_, lean_object* v_state_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_3847_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3853_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_3844_, v_state_3848_, lean_box(0), v_inst_3845_, v___y_3849_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
lean_inc_ref(v___y_3849_);
v___x_3855_ = lean_apply_4(v_handler_3846_, v_a_3852_, v_a_3854_, v___y_3849_, lean_box(0));
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3879_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3858_ = v___x_3855_;
v_isShared_3859_ = v_isSharedCheck_3879_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3879_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v_fst_3860_; lean_object* v_snd_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3878_; 
v_fst_3860_ = lean_ctor_get(v_a_3856_, 0);
v_snd_3861_ = lean_ctor_get(v_a_3856_, 1);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_3856_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3863_ = v_a_3856_;
v_isShared_3864_ = v_isSharedCheck_3878_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_snd_3861_);
lean_inc(v_fst_3860_);
lean_dec(v_a_3856_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3878_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v_response_3865_; uint8_t v_isComplete_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
v_response_3865_ = lean_ctor_get(v_fst_3860_, 0);
lean_inc(v_response_3865_);
v_isComplete_3866_ = lean_ctor_get_uint8(v_fst_3860_, sizeof(void*)*1);
lean_dec(v_fst_3860_);
v___x_3867_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_3865_);
lean_inc(v___x_3867_);
v___x_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
v___x_3869_ = l_Lean_Json_compress(v___x_3867_);
v___x_3870_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3870_, 0, v___x_3868_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
lean_ctor_set_uint8(v___x_3870_, sizeof(void*)*2, v_isComplete_3866_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v_inst_3845_);
v___x_3872_ = v___x_3863_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_inst_3845_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v_snd_3861_);
v___x_3872_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3870_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3873_);
v___x_3875_ = v___x_3858_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_inst_3845_);
v_a_3880_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3855_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3855_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v_a_3852_);
lean_dec_ref(v_handler_3846_);
lean_dec(v_inst_3845_);
v_a_3888_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3853_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3853_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec_ref(v_handler_3846_);
lean_dec(v_inst_3845_);
v_a_3896_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3851_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3851_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_3904_, lean_object* v_inst_3905_, lean_object* v_handler_3906_, lean_object* v_param_3907_, lean_object* v_state_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_3904_, v_inst_3905_, v_handler_3906_, v_param_3907_, v_state_3908_, v___y_3909_);
lean_dec_ref(v___y_3909_);
lean_dec(v_state_3908_);
lean_dec_ref(v_method_3904_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_3912_, lean_object* v_a_x3f_3913_){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_io_basemutex_unlock(v_mutex_3912_);
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_3917_, lean_object* v_a_x3f_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3917_, v_a_x3f_3918_);
lean_dec(v_a_x3f_3918_);
lean_dec(v_mutex_3917_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_3921_, lean_object* v_k_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_ref_3925_; lean_object* v_mutex_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_ref_3925_ = lean_ctor_get(v_mutex_3921_, 0);
lean_inc(v_ref_3925_);
v_mutex_3926_ = lean_ctor_get(v_mutex_3921_, 1);
lean_inc(v_mutex_3926_);
lean_dec_ref(v_mutex_3921_);
v___x_3927_ = lean_io_basemutex_lock(v_mutex_3926_);
lean_inc_ref(v___y_3923_);
v___x_3928_ = lean_apply_3(v_k_3922_, v_ref_3925_, v___y_3923_, lean_box(0));
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3945_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3945_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3945_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
lean_inc(v_a_3929_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set_tag(v___x_3931_, 1);
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
v___x_3935_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3926_, v___x_3934_);
lean_dec_ref(v___x_3934_);
lean_dec(v_mutex_3926_);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; 
v_unused_3943_ = lean_ctor_get(v___x_3935_, 0);
lean_dec(v_unused_3943_);
v___x_3937_ = v___x_3935_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_dec(v___x_3935_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v_a_3929_);
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3929_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
v_a_3946_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3947_ = lean_box(0);
v___x_3948_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3926_, v___x_3947_);
lean_dec(v_mutex_3926_);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; 
v_unused_3956_ = lean_ctor_get(v___x_3948_, 0);
lean_dec(v_unused_3956_);
v___x_3950_ = v___x_3948_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_dec(v___x_3948_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
lean_ctor_set_tag(v___x_3950_, 1);
lean_ctor_set(v___x_3950_, 0, v_a_3946_);
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3946_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_3957_, lean_object* v_k_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_3957_, v_k_3958_, v___y_3959_);
lean_dec_ref(v___y_3959_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_3962_, lean_object* v___f_3963_, lean_object* v_param_3964_, lean_object* v___x_3965_, lean_object* v_x_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_st_ref_get(v_val_3962_);
lean_inc_ref(v___y_3967_);
v___x_3970_ = lean_apply_4(v___f_3963_, v_param_3964_, v___x_3969_, v___y_3967_, lean_box(0));
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3980_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_3980_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3980_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v_snd_3975_; lean_object* v___x_3976_; lean_object* v___x_3978_; 
v_snd_3975_ = lean_ctor_get(v_a_3971_, 1);
lean_inc(v_snd_3975_);
lean_dec(v_a_3971_);
v___x_3976_ = lean_st_ref_swap(v_val_3962_, v_snd_3975_);
lean_dec(v___x_3976_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3965_);
v___x_3978_ = v___x_3973_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3965_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_a_3981_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3970_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3970_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_3989_, lean_object* v___f_3990_, lean_object* v_param_3991_, lean_object* v___x_3992_, lean_object* v_x_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_3989_, v___f_3990_, v_param_3991_, v___x_3992_, v_x_3993_, v___y_3994_);
lean_dec_ref(v___y_3994_);
lean_dec(v_val_3989_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_3997_, lean_object* v___f_3998_, lean_object* v___x_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4003_ = lean_st_ref_get(v___y_4000_);
v___x_4004_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4003_, v___f_3997_, v___y_4001_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4014_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4014_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4014_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4012_; 
v___x_4009_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_3998_, v_a_4005_);
v___x_4010_ = lean_st_ref_swap(v___y_4000_, v___x_4009_);
lean_dec(v___x_4010_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_3999_);
v___x_4012_ = v___x_4007_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_3999_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec_ref(v___f_3998_);
v_a_4015_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4004_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4004_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4023_, lean_object* v___f_4024_, lean_object* v___x_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4023_, v___f_4024_, v___x_4025_, v___y_4026_, v___y_4027_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4030_, lean_object* v___f_4031_, lean_object* v___x_4032_, lean_object* v___f_4033_, lean_object* v_val_4034_, lean_object* v_param_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v___f_4038_; lean_object* v___f_4039_; lean_object* v___x_4040_; 
v___f_4038_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_4038_, 0, v_val_4030_);
lean_closure_set(v___f_4038_, 1, v___f_4031_);
lean_closure_set(v___f_4038_, 2, v_param_4035_);
lean_closure_set(v___f_4038_, 3, v___x_4032_);
v___f_4039_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_4039_, 0, v___f_4038_);
lean_closure_set(v___f_4039_, 1, v___f_4033_);
lean_closure_set(v___f_4039_, 2, v___x_4032_);
v___x_4040_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4034_, v___f_4039_, v___y_4036_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4041_, lean_object* v___f_4042_, lean_object* v___x_4043_, lean_object* v___f_4044_, lean_object* v_val_4045_, lean_object* v_param_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4041_, v___f_4042_, v___x_4043_, v___f_4044_, v_val_4045_, v_param_4046_, v___y_4047_);
lean_dec_ref(v___y_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4050_, lean_object* v_x_4051_){
_start:
{
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4052_, lean_object* v_x_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4052_, v_x_4053_);
lean_dec_ref(v_x_4053_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4055_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4056_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4056_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
v_a_4065_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4056_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4056_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4073_, lean_object* v___f_4074_, lean_object* v_param_4075_, lean_object* v_x_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = lean_st_ref_get(v_val_4073_);
lean_inc_ref(v___y_4077_);
v___x_4080_ = lean_apply_4(v___f_4074_, v_param_4075_, v___x_4079_, v___y_4077_, lean_box(0));
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4091_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4083_ = v___x_4080_;
v_isShared_4084_ = v_isSharedCheck_4091_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4080_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4091_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v_fst_4085_; lean_object* v_snd_4086_; lean_object* v___x_4087_; lean_object* v___x_4089_; 
v_fst_4085_ = lean_ctor_get(v_a_4081_, 0);
lean_inc(v_fst_4085_);
v_snd_4086_ = lean_ctor_get(v_a_4081_, 1);
lean_inc(v_snd_4086_);
lean_dec(v_a_4081_);
v___x_4087_ = lean_st_ref_swap(v_val_4073_, v_snd_4086_);
lean_dec(v___x_4087_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 0, v_fst_4085_);
v___x_4089_ = v___x_4083_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_fst_4085_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
v_a_4092_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4080_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4080_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4100_, lean_object* v___f_4101_, lean_object* v_param_4102_, lean_object* v_x_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4100_, v___f_4101_, v_param_4102_, v_x_4103_, v___y_4104_);
lean_dec_ref(v___y_4104_);
lean_dec(v_val_4100_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4107_, lean_object* v___f_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_st_ref_get(v___y_4109_);
v___x_4113_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4112_, v___f_4107_, v___y_4110_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4123_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4116_ = v___x_4113_;
v_isShared_4117_ = v_isSharedCheck_4123_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4123_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4121_; 
lean_inc(v_a_4114_);
v___x_4118_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4108_, v_a_4114_);
v___x_4119_ = lean_st_ref_swap(v___y_4109_, v___x_4118_);
lean_dec(v___x_4119_);
if (v_isShared_4117_ == 0)
{
v___x_4121_ = v___x_4116_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4114_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
else
{
lean_dec_ref(v___f_4108_);
return v___x_4113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4124_, lean_object* v___f_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4124_, v___f_4125_, v___y_4126_, v___y_4127_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4130_, lean_object* v___f_4131_, lean_object* v___f_4132_, lean_object* v_val_4133_, lean_object* v_param_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___f_4137_; lean_object* v___f_4138_; lean_object* v___x_4139_; 
v___f_4137_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4137_, 0, v_val_4130_);
lean_closure_set(v___f_4137_, 1, v___f_4131_);
lean_closure_set(v___f_4137_, 2, v_param_4134_);
v___f_4138_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4138_, 0, v___f_4137_);
lean_closure_set(v___f_4138_, 1, v___f_4132_);
v___x_4139_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4133_, v___f_4138_, v___y_4135_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4140_, lean_object* v___f_4141_, lean_object* v___f_4142_, lean_object* v_val_4143_, lean_object* v_param_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4140_, v___f_4141_, v___f_4142_, v_val_4143_, v_param_4144_, v___y_4145_);
lean_dec_ref(v___y_4145_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4148_, lean_object* v_inst_4149_, lean_object* v_onDidChange_4150_, lean_object* v_param_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4148_, v___y_4152_, lean_box(0), v_inst_4149_, v___y_4153_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
lean_inc_ref(v___y_4153_);
v___x_4157_ = lean_apply_4(v_onDidChange_4150_, v_param_4151_, v_a_4156_, v___y_4153_, lean_box(0));
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4176_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4160_ = v___x_4157_;
v_isShared_4161_ = v_isSharedCheck_4176_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4176_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v_snd_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4174_; 
v_snd_4162_ = lean_ctor_get(v_a_4158_, 1);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_a_4158_);
if (v_isSharedCheck_4174_ == 0)
{
lean_object* v_unused_4175_; 
v_unused_4175_ = lean_ctor_get(v_a_4158_, 0);
lean_dec(v_unused_4175_);
v___x_4164_ = v_a_4158_;
v_isShared_4165_ = v_isSharedCheck_4174_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_snd_4162_);
lean_dec(v_a_4158_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4174_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 0, v_inst_4149_);
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_inst_4149_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_snd_4162_);
v___x_4167_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4171_; 
v___x_4168_ = lean_box(0);
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
lean_ctor_set(v___x_4169_, 1, v___x_4167_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4169_);
v___x_4171_ = v___x_4160_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec(v_inst_4149_);
v_a_4177_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4157_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4157_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec_ref(v_param_4151_);
lean_dec_ref(v_onDidChange_4150_);
lean_dec(v_inst_4149_);
v_a_4185_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4155_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4155_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4193_, lean_object* v_inst_4194_, lean_object* v_onDidChange_4195_, lean_object* v_param_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4193_, v_inst_4194_, v_onDidChange_4195_, v_param_4196_, v___y_4197_, v___y_4198_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v_method_4193_);
return v_res_4200_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = lean_box(0);
v___x_4204_ = lean_task_pure(v___x_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4210_, lean_object* v_completeness_4211_, lean_object* v_inst_4212_, lean_object* v_initState_4213_, lean_object* v_handler_4214_, lean_object* v_onDidChange_4215_){
_start:
{
uint8_t v___x_4217_; 
v___x_4217_ = l_Lean_initializing();
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
lean_dec_ref(v_onDidChange_4215_);
lean_dec_ref(v_handler_4214_);
lean_dec(v_initState_4213_);
lean_dec(v_inst_4212_);
lean_dec(v_completeness_4211_);
v___x_4218_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4219_ = lean_string_append(v___x_4218_, v_method_4210_);
lean_dec_ref(v_method_4210_);
v___x_4220_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4221_ = lean_string_append(v___x_4219_, v___x_4220_);
v___x_4222_ = lean_mk_io_user_error(v___x_4221_);
v___x_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
return v___x_4223_;
}
else
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___f_4231_; lean_object* v___f_4232_; lean_object* v___f_4233_; lean_object* v___f_4234_; lean_object* v___f_4235_; lean_object* v___f_4236_; lean_object* v___f_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4224_ = lean_box(0);
v___x_4225_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2);
v___x_4226_ = l_Std_Mutex_new___redArg(v___x_4225_);
lean_inc_n(v_inst_4212_, 2);
v___x_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4227_, 0, v_inst_4212_);
lean_ctor_set(v___x_4227_, 1, v_initState_4213_);
lean_inc_ref(v___x_4227_);
v___x_4228_ = lean_st_mk_ref(v___x_4227_);
v___x_4229_ = l_Lean_Server_statefulRequestHandlers;
v___x_4230_ = lean_st_ref_take(v___x_4229_);
v___f_4231_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
lean_inc_ref_n(v_method_4210_, 2);
v___f_4232_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4232_, 0, v_method_4210_);
lean_closure_set(v___f_4232_, 1, v_inst_4212_);
lean_closure_set(v___f_4232_, 2, v_handler_4214_);
v___f_4233_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4233_, 0, v_method_4210_);
lean_closure_set(v___f_4233_, 1, v_inst_4212_);
lean_closure_set(v___f_4233_, 2, v_onDidChange_4215_);
v___f_4234_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___f_4235_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
lean_inc_ref_n(v___x_4226_, 2);
lean_inc_ref(v___f_4232_);
lean_inc_n(v___x_4228_, 2);
v___f_4236_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4236_, 0, v___x_4228_);
lean_closure_set(v___f_4236_, 1, v___f_4232_);
lean_closure_set(v___f_4236_, 2, v___f_4234_);
lean_closure_set(v___f_4236_, 3, v___x_4226_);
lean_inc_ref(v___f_4233_);
v___f_4237_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_4237_, 0, v___x_4228_);
lean_closure_set(v___f_4237_, 1, v___f_4233_);
lean_closure_set(v___f_4237_, 2, v___x_4224_);
lean_closure_set(v___f_4237_, 3, v___f_4235_);
lean_closure_set(v___f_4237_, 4, v___x_4226_);
v___x_4238_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4238_, 0, v___f_4231_);
lean_ctor_set(v___x_4238_, 1, v___f_4232_);
lean_ctor_set(v___x_4238_, 2, v___f_4236_);
lean_ctor_set(v___x_4238_, 3, v___f_4233_);
lean_ctor_set(v___x_4238_, 4, v___f_4237_);
lean_ctor_set(v___x_4238_, 5, v___x_4226_);
lean_ctor_set(v___x_4238_, 6, v___x_4227_);
lean_ctor_set(v___x_4238_, 7, v___x_4228_);
lean_ctor_set(v___x_4238_, 8, v_completeness_4211_);
v___x_4239_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4230_, v_method_4210_, v___x_4238_);
v___x_4240_ = lean_st_ref_put(v___x_4229_, v___x_4239_);
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
return v___x_4241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4242_, lean_object* v_completeness_4243_, lean_object* v_inst_4244_, lean_object* v_initState_4245_, lean_object* v_handler_4246_, lean_object* v_onDidChange_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4242_, v_completeness_4243_, v_inst_4244_, v_initState_4245_, v_handler_4246_, v_onDidChange_4247_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4251_, lean_object* v_completeness_4252_, lean_object* v_inst_4253_, lean_object* v_initState_4254_, lean_object* v_handler_4255_, lean_object* v_onDidChange_4256_){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; uint8_t v___x_4260_; 
v___x_4258_ = l_Lean_Server_requestHandlers;
v___x_4259_ = lean_st_ref_get(v___x_4258_);
v___x_4260_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4259_, v_method_4251_);
lean_dec(v___x_4259_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; 
v___x_4261_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4251_, v_completeness_4252_, v_inst_4253_, v_initState_4254_, v_handler_4255_, v_onDidChange_4256_);
return v___x_4261_;
}
else
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_dec_ref(v_onDidChange_4256_);
lean_dec_ref(v_handler_4255_);
lean_dec(v_initState_4254_);
lean_dec(v_inst_4253_);
lean_dec(v_completeness_4252_);
v___x_4262_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4263_ = lean_string_append(v___x_4262_, v_method_4251_);
lean_dec_ref(v_method_4251_);
v___x_4264_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4265_ = lean_string_append(v___x_4263_, v___x_4264_);
v___x_4266_ = lean_mk_io_user_error(v___x_4265_);
v___x_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
return v___x_4267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4268_, lean_object* v_completeness_4269_, lean_object* v_inst_4270_, lean_object* v_initState_4271_, lean_object* v_handler_4272_, lean_object* v_onDidChange_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4268_, v_completeness_4269_, v_inst_4270_, v_initState_4271_, v_handler_4272_, v_onDidChange_4273_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4276_, lean_object* v_refreshMethod_4277_, lean_object* v_refreshIntervalMs_4278_, lean_object* v_inst_4279_, lean_object* v_initState_4280_, lean_object* v_handler_4281_, lean_object* v_onDidChange_4282_){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4284_, 0, v_refreshMethod_4277_);
lean_ctor_set(v___x_4284_, 1, v_refreshIntervalMs_4278_);
v___x_4285_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4276_, v___x_4284_, v_inst_4279_, v_initState_4280_, v_handler_4281_, v_onDidChange_4282_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4286_, lean_object* v_refreshMethod_4287_, lean_object* v_refreshIntervalMs_4288_, lean_object* v_inst_4289_, lean_object* v_initState_4290_, lean_object* v_handler_4291_, lean_object* v_onDidChange_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4286_, v_refreshMethod_4287_, v_refreshIntervalMs_4288_, v_inst_4289_, v_initState_4290_, v_handler_4291_, v_onDidChange_4292_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4295_){
_start:
{
lean_object* v___x_4296_; 
lean_inc(v_params_4295_);
v___x_4296_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4295_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4312_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4312_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4312_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
uint8_t v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4301_ = 3;
v___x_4302_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4303_ = l_Lean_Json_compress(v_params_4295_);
v___x_4304_ = lean_string_append(v___x_4302_, v___x_4303_);
lean_dec_ref(v___x_4303_);
v___x_4305_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_4306_ = lean_string_append(v___x_4304_, v___x_4305_);
v___x_4307_ = lean_string_append(v___x_4306_, v_a_4297_);
lean_dec(v_a_4297_);
v___x_4308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set_uint8(v___x_4308_, sizeof(void*)*1, v___x_4301_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4308_);
v___x_4310_ = v___x_4299_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
lean_dec(v_params_4295_);
v_a_4313_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4296_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4296_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4321_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4321_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4339_; 
v_a_4331_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4333_ = v___x_4322_;
v_isShared_4334_ = v_isSharedCheck_4339_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4322_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4339_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v_textDocument_4335_; lean_object* v___x_4337_; 
v_textDocument_4335_ = lean_ctor_get(v_a_4331_, 0);
lean_inc_ref(v_textDocument_4335_);
lean_dec(v_a_4331_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 0, v_textDocument_4335_);
v___x_4337_ = v___x_4333_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_textDocument_4335_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4340_, uint8_t v_val_4341_, lean_object* v___y_4342_){
_start:
{
if (lean_obj_tag(v___y_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec(v_serialize_x3f_4340_);
v_a_4343_ = lean_ctor_get(v___y_4342_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___y_4342_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___y_4342_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___y_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4340_) == 1)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4362_; 
v_a_4351_ = lean_ctor_get(v___y_4342_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___y_4342_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4353_ = v___y_4342_;
v_isShared_4354_ = v_isSharedCheck_4362_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___y_4342_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4362_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v_val_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4360_; 
v_val_4355_ = lean_ctor_get(v_serialize_x3f_4340_, 0);
lean_inc(v_val_4355_);
lean_dec_ref_known(v_serialize_x3f_4340_, 1);
v___x_4356_ = lean_box(0);
v___x_4357_ = lean_apply_1(v_val_4355_, v_a_4351_);
v___x_4358_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4358_, 0, v___x_4356_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
lean_ctor_set_uint8(v___x_4358_, sizeof(void*)*2, v_val_4341_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4358_);
v___x_4360_ = v___x_4353_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4374_; 
lean_dec(v_serialize_x3f_4340_);
v_a_4363_ = lean_ctor_get(v___y_4342_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___y_4342_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4365_ = v___y_4342_;
v_isShared_4366_ = v_isSharedCheck_4374_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___y_4342_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4374_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; 
v___x_4367_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4363_);
lean_inc(v___x_4367_);
v___x_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
v___x_4369_ = l_Lean_Json_compress(v___x_4367_);
v___x_4370_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
lean_ctor_set_uint8(v___x_4370_, sizeof(void*)*2, v_val_4341_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v___x_4370_);
v___x_4372_ = v___x_4365_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4370_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4375_, lean_object* v_val_4376_, lean_object* v___y_4377_){
_start:
{
uint8_t v_val_3648__boxed_4378_; lean_object* v_res_4379_; 
v_val_3648__boxed_4378_ = lean_unbox(v_val_4376_);
v_res_4379_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4375_, v_val_3648__boxed_4378_, v___y_4377_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4380_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4380_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4382_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4382_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
lean_ctor_set_tag(v___x_4385_, 1);
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
v_a_4391_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4382_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4382_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
lean_ctor_set_tag(v___x_4393_, 0);
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4399_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4402_, lean_object* v___f_4403_, lean_object* v_j_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4404_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4409_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4407_, 1);
lean_inc_ref(v___y_4405_);
v___x_4409_ = lean_apply_3(v_handler_4402_, v_a_4408_, v___y_4405_, lean_box(0));
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4418_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4412_ = v___x_4409_;
v_isShared_4413_ = v_isSharedCheck_4418_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4418_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4414_; lean_object* v___x_4416_; 
v___x_4414_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4403_, v_a_4410_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4414_);
v___x_4416_ = v___x_4412_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v___f_4403_);
v_a_4419_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4409_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4409_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec_ref(v___f_4403_);
lean_dec_ref(v_handler_4402_);
v_a_4427_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4407_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4407_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_4435_, lean_object* v___f_4436_, lean_object* v_j_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4435_, v___f_4436_, v_j_4437_, v___y_4438_);
lean_dec_ref(v___y_4438_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_4443_, lean_object* v_handler_4444_, lean_object* v_serialize_x3f_4445_){
_start:
{
uint8_t v___x_4447_; 
v___x_4447_ = l_Lean_initializing();
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
lean_dec(v_serialize_x3f_4445_);
lean_dec_ref(v_handler_4444_);
v___x_4448_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4449_ = lean_string_append(v___x_4448_, v_method_4443_);
lean_dec_ref(v_method_4443_);
v___x_4450_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4451_ = lean_string_append(v___x_4449_, v___x_4450_);
v___x_4452_ = lean_mk_io_user_error(v___x_4451_);
v___x_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
return v___x_4453_;
}
else
{
lean_object* v___x_4454_; lean_object* v___x_4455_; uint8_t v___x_4456_; 
v___x_4454_ = l_Lean_Server_requestHandlers;
v___x_4455_ = lean_st_ref_get(v___x_4454_);
v___x_4456_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4455_, v_method_4443_);
lean_dec(v___x_4455_);
if (v___x_4456_ == 0)
{
lean_object* v___x_4457_; lean_object* v___f_4458_; lean_object* v___x_4459_; lean_object* v___f_4460_; lean_object* v___f_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4457_ = lean_st_ref_take(v___x_4454_);
v___f_4458_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4459_ = lean_box(v___x_4447_);
v___f_4460_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4460_, 0, v_serialize_x3f_4445_);
lean_closure_set(v___f_4460_, 1, v___x_4459_);
v___f_4461_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4461_, 0, v_handler_4444_);
lean_closure_set(v___f_4461_, 1, v___f_4460_);
v___x_4462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4462_, 0, v___f_4458_);
lean_ctor_set(v___x_4462_, 1, v___f_4461_);
v___x_4463_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4457_, v_method_4443_, v___x_4462_);
v___x_4464_ = lean_st_ref_put(v___x_4454_, v___x_4463_);
v___x_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
return v___x_4465_;
}
else
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_dec(v_serialize_x3f_4445_);
lean_dec_ref(v_handler_4444_);
v___x_4466_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4467_ = lean_string_append(v___x_4466_, v_method_4443_);
lean_dec_ref(v_method_4443_);
v___x_4468_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4469_ = lean_string_append(v___x_4467_, v___x_4468_);
v___x_4470_ = lean_mk_io_user_error(v___x_4469_);
v___x_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4472_, lean_object* v_handler_4473_, lean_object* v_serialize_x3f_4474_, lean_object* v_a_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_4472_, v_handler_4473_, v_serialize_x3f_4474_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4484_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4485_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4486_ = lean_box(0);
v___x_4487_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_4484_, v___x_4485_, v___x_4486_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
lean_dec_ref_known(v___x_4487_, 1);
v___x_4488_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_4489_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4490_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4491_ = lean_unsigned_to_nat(2000u);
v___x_4492_ = lean_box(0);
v___x_4493_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4494_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4495_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_4489_, v___x_4490_, v___x_4491_, v___x_4488_, v___x_4492_, v___x_4493_, v___x_4494_);
return v___x_4495_;
}
else
{
return v___x_4487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_4498_, lean_object* v_refreshMethod_4499_, lean_object* v_refreshIntervalMs_4500_, lean_object* v_stateType_4501_, lean_object* v_inst_4502_, lean_object* v_initState_4503_, lean_object* v_handler_4504_, lean_object* v_onDidChange_4505_){
_start:
{
lean_object* v___x_4507_; 
v___x_4507_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4498_, v_refreshMethod_4499_, v_refreshIntervalMs_4500_, v_inst_4502_, v_initState_4503_, v_handler_4504_, v_onDidChange_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_4508_, lean_object* v_refreshMethod_4509_, lean_object* v_refreshIntervalMs_4510_, lean_object* v_stateType_4511_, lean_object* v_inst_4512_, lean_object* v_initState_4513_, lean_object* v_handler_4514_, lean_object* v_onDidChange_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_4508_, v_refreshMethod_4509_, v_refreshIntervalMs_4510_, v_stateType_4511_, v_inst_4512_, v_initState_4513_, v_handler_4514_, v_onDidChange_4515_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4518_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_4522_, v_a_4523_);
lean_dec_ref(v_a_4523_);
return v_res_4525_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_4526_, lean_object* v_x_4527_, lean_object* v_x_4528_){
_start:
{
uint8_t v___x_4529_; 
v___x_4529_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4527_, v_x_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_4530_, lean_object* v_x_4531_, lean_object* v_x_4532_){
_start:
{
uint8_t v_res_4533_; lean_object* v_r_4534_; 
v_res_4533_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_4530_, v_x_4531_, v_x_4532_);
lean_dec_ref(v_x_4532_);
lean_dec_ref(v_x_4531_);
v_r_4534_ = lean_box(v_res_4533_);
return v_r_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_4535_, lean_object* v_x_4536_, lean_object* v_x_4537_, lean_object* v_x_4538_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4536_, v_x_4537_, v_x_4538_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_4540_, lean_object* v_completeness_4541_, lean_object* v_stateType_4542_, lean_object* v_inst_4543_, lean_object* v_initState_4544_, lean_object* v_handler_4545_, lean_object* v_onDidChange_4546_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4540_, v_completeness_4541_, v_inst_4543_, v_initState_4544_, v_handler_4545_, v_onDidChange_4546_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_4549_, lean_object* v_completeness_4550_, lean_object* v_stateType_4551_, lean_object* v_inst_4552_, lean_object* v_initState_4553_, lean_object* v_handler_4554_, lean_object* v_onDidChange_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_4549_, v_completeness_4550_, v_stateType_4551_, v_inst_4552_, v_initState_4553_, v_handler_4554_, v_onDidChange_4555_);
return v_res_4557_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_4558_, lean_object* v_x_4559_, size_t v_x_4560_, lean_object* v_x_4561_){
_start:
{
uint8_t v___x_4562_; 
v___x_4562_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4559_, v_x_4560_, v_x_4561_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4563_, lean_object* v_x_4564_, lean_object* v_x_4565_, lean_object* v_x_4566_){
_start:
{
size_t v_x_3967__boxed_4567_; uint8_t v_res_4568_; lean_object* v_r_4569_; 
v_x_3967__boxed_4567_ = lean_unbox_usize(v_x_4565_);
lean_dec(v_x_4565_);
v_res_4568_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_4563_, v_x_4564_, v_x_3967__boxed_4567_, v_x_4566_);
lean_dec_ref(v_x_4566_);
lean_dec_ref(v_x_4564_);
v_r_4569_ = lean_box(v_res_4568_);
return v_r_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_4570_, lean_object* v_x_4571_, size_t v_x_4572_, size_t v_x_4573_, lean_object* v_x_4574_, lean_object* v_x_4575_){
_start:
{
lean_object* v___x_4576_; 
v___x_4576_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4571_, v_x_4572_, v_x_4573_, v_x_4574_, v_x_4575_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4577_, lean_object* v_x_4578_, lean_object* v_x_4579_, lean_object* v_x_4580_, lean_object* v_x_4581_, lean_object* v_x_4582_){
_start:
{
size_t v_x_3978__boxed_4583_; size_t v_x_3979__boxed_4584_; lean_object* v_res_4585_; 
v_x_3978__boxed_4583_ = lean_unbox_usize(v_x_4579_);
lean_dec(v_x_4579_);
v_x_3979__boxed_4584_ = lean_unbox_usize(v_x_4580_);
lean_dec(v_x_4580_);
v_res_4585_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_4577_, v_x_4578_, v_x_3978__boxed_4583_, v_x_3979__boxed_4584_, v_x_4581_, v_x_4582_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_4586_, lean_object* v_00_u03b2_4587_, lean_object* v_mutex_4588_, lean_object* v_k_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4588_, v_k_4589_, v___y_4590_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_4593_, lean_object* v_00_u03b2_4594_, lean_object* v_mutex_4595_, lean_object* v_k_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_4593_, v_00_u03b2_4594_, v_mutex_4595_, v_k_4596_, v___y_4597_);
lean_dec_ref(v___y_4597_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_4600_, lean_object* v_completeness_4601_, lean_object* v_stateType_4602_, lean_object* v_inst_4603_, lean_object* v_initState_4604_, lean_object* v_handler_4605_, lean_object* v_onDidChange_4606_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4600_, v_completeness_4601_, v_inst_4603_, v_initState_4604_, v_handler_4605_, v_onDidChange_4606_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_4609_, lean_object* v_completeness_4610_, lean_object* v_stateType_4611_, lean_object* v_inst_4612_, lean_object* v_initState_4613_, lean_object* v_handler_4614_, lean_object* v_onDidChange_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_4609_, v_completeness_4610_, v_stateType_4611_, v_inst_4612_, v_initState_4613_, v_handler_4614_, v_onDidChange_4615_);
return v_res_4617_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4618_, lean_object* v_keys_4619_, lean_object* v_vals_4620_, lean_object* v_heq_4621_, lean_object* v_i_4622_, lean_object* v_k_4623_){
_start:
{
uint8_t v___x_4624_; 
v___x_4624_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4619_, v_i_4622_, v_k_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4625_, lean_object* v_keys_4626_, lean_object* v_vals_4627_, lean_object* v_heq_4628_, lean_object* v_i_4629_, lean_object* v_k_4630_){
_start:
{
uint8_t v_res_4631_; lean_object* v_r_4632_; 
v_res_4631_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_4625_, v_keys_4626_, v_vals_4627_, v_heq_4628_, v_i_4629_, v_k_4630_);
lean_dec_ref(v_k_4630_);
lean_dec_ref(v_vals_4627_);
lean_dec_ref(v_keys_4626_);
v_r_4632_ = lean_box(v_res_4631_);
return v_r_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4633_, lean_object* v_n_4634_, lean_object* v_k_4635_, lean_object* v_v_4636_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_4634_, v_k_4635_, v_v_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4638_, size_t v_depth_4639_, lean_object* v_keys_4640_, lean_object* v_vals_4641_, lean_object* v_heq_4642_, lean_object* v_i_4643_, lean_object* v_entries_4644_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_4639_, v_keys_4640_, v_vals_4641_, v_i_4643_, v_entries_4644_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_4646_, lean_object* v_depth_4647_, lean_object* v_keys_4648_, lean_object* v_vals_4649_, lean_object* v_heq_4650_, lean_object* v_i_4651_, lean_object* v_entries_4652_){
_start:
{
size_t v_depth_boxed_4653_; lean_object* v_res_4654_; 
v_depth_boxed_4653_ = lean_unbox_usize(v_depth_4647_);
lean_dec(v_depth_4647_);
v_res_4654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_4646_, v_depth_boxed_4653_, v_keys_4648_, v_vals_4649_, v_heq_4650_, v_i_4651_, v_entries_4652_);
lean_dec_ref(v_vals_4649_);
lean_dec_ref(v_keys_4648_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_4655_, lean_object* v_a_4656_){
_start:
{
lean_object* v___x_4658_; 
v___x_4658_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4655_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_4659_, v_a_4660_);
lean_dec_ref(v_a_4660_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_4663_, lean_object* v_x_4664_, lean_object* v_x_4665_, lean_object* v_x_4666_, lean_object* v_x_4667_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_4664_, v_x_4665_, v_x_4666_, v_x_4667_);
return v___x_4668_;
}
}
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_View(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_keywordSemanticTokenMap = _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap();
lean_mark_persistent(l_Lean_Server_FileWorker_keywordSemanticTokenMap);
l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default = _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default);
l_Lean_Server_FileWorker_instInhabitedSemanticTokensState = _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedSemanticTokensState);
res = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Requests(uint8_t builtin);
lean_object* initialize_Lean_DocString_View(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_SemanticHighlighting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_SemanticHighlighting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_SemanticHighlighting(builtin);
}
#ifdef __cplusplus
}
#endif

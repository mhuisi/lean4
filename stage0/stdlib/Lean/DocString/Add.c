// Lean compiler output
// Module: Lean.DocString.Add
// Imports: import Lean.Elab.DocString public import Lean.DocString.DeferredCheck public import Lean.DocString.Parser public import Lean.Elab.Term.TermElabM
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Doc_deferredCheckExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Doc_Parser_BlockCtxt_forDocString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_documentFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* l_Lean_Doc_Parser_blockFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_locateError(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabModSnippet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object*);
lean_object* l_Lean_getMainModuleDoc(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_versoDocStringExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_docStringExt;
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_exec___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toArray(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
uint8_t l_Lean_isVersoDocComment(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findInternalDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_removeBuiltinDocString(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_parseErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_parseErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unexpected '"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__4___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "Documentation comment has no source location, cannot parse"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__10___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__10___closed__0_value;
static lean_once_cell_t l_Lean_parseVersoDocString___redArg___lam__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_parseVersoDocString___redArg___lam__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_document_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_document_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_parseFailure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_parseFailure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_VersoDocstringView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_VersoDocstringView_of___closed__0 = (const lean_object*)&l_Lean_VersoDocstringView_of___closed__0_value;
static const lean_string_object l_Lean_VersoDocstringView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_VersoDocstringView_of___closed__1 = (const lean_object*)&l_Lean_VersoDocstringView_of___closed__1_value;
static const lean_string_object l_Lean_VersoDocstringView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_VersoDocstringView_of___closed__2 = (const lean_object*)&l_Lean_VersoDocstringView_of___closed__2_value;
static const lean_string_object l_Lean_VersoDocstringView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "parseFailure"};
static const lean_object* l_Lean_VersoDocstringView_of___closed__3 = (const lean_object*)&l_Lean_VersoDocstringView_of___closed__3_value;
static const lean_ctor_object l_Lean_VersoDocstringView_of___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_VersoDocstringView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_VersoDocstringView_of___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_VersoDocstringView_of___closed__4_value_aux_0),((lean_object*)&l_Lean_VersoDocstringView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_VersoDocstringView_of___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_VersoDocstringView_of___closed__4_value_aux_1),((lean_object*)&l_Lean_VersoDocstringView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_VersoDocstringView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_VersoDocstringView_of___closed__4_value_aux_2),((lean_object*)&l_Lean_VersoDocstringView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 162, 159, 121, 181, 7, 46, 32)}};
static const lean_object* l_Lean_VersoDocstringView_of___closed__4 = (const lean_object*)&l_Lean_VersoDocstringView_of___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_versoDocStringOfText___closed__0 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__0_value;
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 8, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringOfText___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_versoDocStringOfText___closed__1 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__1_value;
static const lean_closure_object l_Lean_versoDocStringOfText___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_documentFn, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_versoDocStringOfText___closed__1_value)} };
static const lean_object* l_Lean_versoDocStringOfText___closed__2 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__2_value;
static const lean_array_object l_Lean_versoDocStringOfText___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_versoDocStringOfText___closed__3 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__3_value;
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_versoDocStringOfText___closed__3_value),((lean_object*)&l_Lean_versoDocStringOfText___closed__3_value)}};
static const lean_object* l_Lean_versoDocStringOfText___closed__4 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__4_value;
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_versoDocStringOfText___closed__4_value),((lean_object*)&l_Lean_versoDocStringOfText___closed__3_value)}};
static const lean_object* l_Lean_versoDocStringOfText___closed__5 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_versoDocString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_versoDocString___closed__0 = (const lean_object*)&l_Lean_versoDocString___closed__0_value;
static const lean_string_object l_Lean_versoDocString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_versoDocString___closed__1 = (const lean_object*)&l_Lean_versoDocString___closed__1_value;
static const lean_string_object l_Lean_versoDocString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_versoDocString___closed__2 = (const lean_object*)&l_Lean_versoDocString___closed__2_value;
static const lean_ctor_object l_Lean_versoDocString___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_VersoDocstringView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_versoDocString___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__3_value_aux_0),((lean_object*)&l_Lean_versoDocString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_versoDocString___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__3_value_aux_1),((lean_object*)&l_Lean_versoDocString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_versoDocString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__3_value_aux_2),((lean_object*)&l_Lean_versoDocString___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l_Lean_versoDocString___closed__3 = (const lean_object*)&l_Lean_versoDocString___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_versoDocStringFromString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_versoDocStringFromString___closed__0 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__0_value;
static const lean_string_object l_Lean_versoDocStringFromString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_versoDocStringFromString___closed__1 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__1_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_versoDocStringFromString___closed__2 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__2_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__2_value),((lean_object*)&l_Lean_versoDocStringFromString___closed__0_value)}};
static const lean_object* l_Lean_versoDocStringFromString___closed__3 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration `"};
static const lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__1;
static const lean_string_object l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is in an imported module"};
static const lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration '"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is in an imported module"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Error adding module docs: "};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "Can't add Verso-format module docs because there is already Markdown-format content present."};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "invalid doc string removal, declaration `"};
static const lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0 = (const lean_object*)&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_makeDocStringVerso___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Documentation for `"};
static const lean_object* l_Lean_makeDocStringVerso___closed__0 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__0_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__1;
static const lean_string_object l_Lean_makeDocStringVerso___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is already in Verso format"};
static const lean_object* l_Lean_makeDocStringVerso___closed__2 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__2_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__3;
static const lean_string_object l_Lean_makeDocStringVerso___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "No documentation found for `"};
static const lean_object* l_Lean_makeDocStringVerso___closed__4 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__4_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__5;
static const lean_string_object l_Lean_makeDocStringVerso___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_makeDocStringVerso___closed__6 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__6_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__7;
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_____s_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1(lean_object* v___x_5_, lean_object* v_toPure_6_, lean_object* v_r_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_5_);
v___x_9_ = lean_apply_2(v_toPure_6_, lean_box(0), v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3(lean_object* v___y_10_, lean_object* v_str_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_toBind_16_, lean_object* v___f_17_, lean_object* v___f_18_, lean_object* v_a_19_, lean_object* v_x_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_fst_22_; 
v_fst_22_ = lean_ctor_get(v_a_19_, 0);
lean_inc(v_fst_22_);
if (lean_obj_tag(v___y_10_) == 1)
{
lean_object* v_snd_23_; lean_object* v_start_24_; lean_object* v_stop_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_48_; 
lean_dec(v___f_18_);
v_snd_23_ = lean_ctor_get(v_a_19_, 1);
lean_inc(v_snd_23_);
lean_dec_ref(v_a_19_);
v_start_24_ = lean_ctor_get(v_fst_22_, 0);
v_stop_25_ = lean_ctor_get(v_fst_22_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_fst_22_);
if (v_isSharedCheck_48_ == 0)
{
v___x_27_ = v_fst_22_;
v_isShared_28_ = v_isSharedCheck_48_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_stop_25_);
lean_inc(v_start_24_);
lean_dec(v_fst_22_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_48_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_val_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_47_; 
v_val_29_ = lean_ctor_get(v___y_10_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___y_10_);
if (v_isSharedCheck_47_ == 0)
{
v___x_31_ = v___y_10_;
v_isShared_32_ = v_isSharedCheck_47_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_val_29_);
lean_dec(v___y_10_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_47_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_33_ = lean_nat_add(v_val_29_, v_start_24_);
v___x_34_ = lean_nat_add(v_val_29_, v_stop_25_);
lean_dec(v_val_29_);
v___x_35_ = 0;
v___x_36_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_36_, 0, v___x_33_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
lean_ctor_set_uint8(v___x_36_, sizeof(void*)*2, v___x_35_);
v___x_37_ = lean_string_utf8_extract(v_str_11_, v_start_24_, v_stop_25_);
lean_dec(v_stop_25_);
lean_dec(v_start_24_);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 2);
lean_ctor_set(v___x_27_, 1, v___x_37_);
lean_ctor_set(v___x_27_, 0, v___x_36_);
v___x_39_ = v___x_27_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_37_);
v___x_39_ = v_reuseFailAlloc_46_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_41_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 3);
lean_ctor_set(v___x_31_, 0, v_snd_23_);
v___x_41_ = v___x_31_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_snd_23_);
v___x_41_ = v_reuseFailAlloc_45_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = l_Lean_MessageData_ofFormat(v___x_41_);
v___x_43_ = l_Lean_logErrorAt___redArg(v_inst_12_, v_inst_13_, v_inst_14_, v_inst_15_, v___x_39_, v___x_42_);
v___x_44_ = lean_apply_4(v_toBind_16_, lean_box(0), lean_box(0), v___x_43_, v___f_17_);
return v___x_44_;
}
}
}
}
}
else
{
lean_object* v_snd_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_fst_22_);
lean_dec(v___f_17_);
lean_dec(v___y_10_);
v_snd_49_ = lean_ctor_get(v_a_19_, 1);
lean_inc(v_snd_49_);
lean_dec_ref(v_a_19_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v_snd_49_);
v___x_51_ = l_Lean_MessageData_ofFormat(v___x_50_);
v___x_52_ = l_Lean_logError___redArg(v_inst_12_, v_inst_13_, v_inst_14_, v_inst_15_, v___x_51_);
v___x_53_ = lean_apply_4(v_toBind_16_, lean_box(0), lean_box(0), v___x_52_, v___f_18_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3___boxed(lean_object* v___y_54_, lean_object* v_str_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_toBind_60_, lean_object* v___f_61_, lean_object* v___f_62_, lean_object* v_a_63_, lean_object* v_x_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_validateDocComment___redArg___lam__3(v___y_54_, v_str_55_, v_inst_56_, v_inst_57_, v_inst_58_, v_inst_59_, v_toBind_60_, v___f_61_, v___f_62_, v_a_63_, v_x_64_, v___y_65_);
lean_dec_ref(v_str_55_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2(lean_object* v_toPure_67_, lean_object* v___y_68_, lean_object* v_str_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_toBind_74_, lean_object* v___f_75_, lean_object* v_____x_76_){
_start:
{
lean_object* v_fst_77_; lean_object* v___x_78_; lean_object* v___f_79_; lean_object* v___f_80_; size_t v_sz_81_; size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_fst_77_ = lean_ctor_get(v_____x_76_, 0);
lean_inc(v_fst_77_);
lean_dec_ref(v_____x_76_);
v___x_78_ = lean_box(0);
v___f_79_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__1), 3, 2);
lean_closure_set(v___f_79_, 0, v___x_78_);
lean_closure_set(v___f_79_, 1, v_toPure_67_);
lean_inc_ref(v___f_79_);
lean_inc(v_toBind_74_);
lean_inc_ref(v_inst_70_);
v___f_80_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__3___boxed), 12, 9);
lean_closure_set(v___f_80_, 0, v___y_68_);
lean_closure_set(v___f_80_, 1, v_str_69_);
lean_closure_set(v___f_80_, 2, v_inst_70_);
lean_closure_set(v___f_80_, 3, v_inst_71_);
lean_closure_set(v___f_80_, 4, v_inst_72_);
lean_closure_set(v___f_80_, 5, v_inst_73_);
lean_closure_set(v___f_80_, 6, v_toBind_74_);
lean_closure_set(v___f_80_, 7, v___f_79_);
lean_closure_set(v___f_80_, 8, v___f_79_);
v_sz_81_ = lean_array_size(v_fst_77_);
v___x_82_ = ((size_t)0ULL);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_70_, v_fst_77_, v___f_80_, v_sz_81_, v___x_82_, v___x_78_);
v___x_84_ = lean_apply_4(v_toBind_74_, lean_box(0), lean_box(0), v___x_83_, v___f_75_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_docstring_90_){
_start:
{
lean_object* v_toApplicative_91_; lean_object* v_toBind_92_; lean_object* v_toPure_93_; lean_object* v_str_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___y_100_; 
v_toApplicative_91_ = lean_ctor_get(v_inst_85_, 0);
v_toBind_92_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_toBind_92_);
v_toPure_93_ = lean_ctor_get(v_toApplicative_91_, 1);
lean_inc_n(v_toPure_93_, 2);
v_str_94_ = l_Lean_TSyntax_getDocString(v_docstring_90_);
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = l_Lean_Syntax_getArg(v_docstring_90_, v___x_95_);
v___x_97_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_96_);
lean_dec(v___x_96_);
v___f_98_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_98_, 0, v_toPure_93_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(0);
v___y_100_ = v___x_106_;
goto v___jp_99_;
}
else
{
lean_object* v_val_107_; uint8_t v___x_108_; lean_object* v___x_109_; 
v_val_107_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v___x_97_, 1);
v___x_108_ = 0;
v___x_109_ = l_Lean_SourceInfo_getPos_x3f(v_val_107_, v___x_108_);
lean_dec(v_val_107_);
v___y_100_ = v___x_109_;
goto v___jp_99_;
}
v___jp_99_:
{
lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_inc(v_toBind_92_);
lean_inc_ref(v_str_94_);
v___f_101_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__2), 10, 9);
lean_closure_set(v___f_101_, 0, v_toPure_93_);
lean_closure_set(v___f_101_, 1, v___y_100_);
lean_closure_set(v___f_101_, 2, v_str_94_);
lean_closure_set(v___f_101_, 3, v_inst_85_);
lean_closure_set(v___f_101_, 4, v_inst_87_);
lean_closure_set(v___f_101_, 5, v_inst_88_);
lean_closure_set(v___f_101_, 6, v_inst_89_);
lean_closure_set(v___f_101_, 7, v_toBind_92_);
lean_closure_set(v___f_101_, 8, v___f_98_);
v___x_102_ = l_Lean_rewriteManualLinksCore(v_str_94_);
v___x_103_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_103_, 0, lean_box(0));
lean_closure_set(v___x_103_, 1, lean_box(0));
lean_closure_set(v___x_103_, 2, v___x_102_);
v___x_104_ = lean_apply_2(v_inst_86_, lean_box(0), v___x_103_);
v___x_105_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_104_, v___f_101_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_docstring_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_validateDocComment___redArg(v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_, v_inst_114_, v_docstring_115_);
lean_dec(v_docstring_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object* v_m_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_docstring_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_validateDocComment___redArg(v_inst_118_, v_inst_119_, v_inst_120_, v_inst_121_, v_inst_122_, v_docstring_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_docstring_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_validateDocComment(v_m_125_, v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_, v_inst_130_, v_docstring_131_);
lean_dec(v_docstring_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(lean_object* v_ictx_134_, lean_object* v_pos_135_, lean_object* v_e_136_){
_start:
{
lean_object* v___x_137_; lean_object* v_snd_138_; lean_object* v_fst_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v_fileName_142_; lean_object* v_fileMap_143_; lean_object* v___x_144_; lean_object* v___y_146_; 
v___x_137_ = l_Lean_Doc_Parser_locateError(v_ictx_134_, v_pos_135_, v_e_136_);
v_snd_138_ = lean_ctor_get(v___x_137_, 1);
lean_inc(v_snd_138_);
v_fst_139_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_fst_139_);
lean_dec_ref(v___x_137_);
v_fst_140_ = lean_ctor_get(v_snd_138_, 0);
lean_inc(v_fst_140_);
v_snd_141_ = lean_ctor_get(v_snd_138_, 1);
lean_inc(v_snd_141_);
lean_dec(v_snd_138_);
v_fileName_142_ = lean_ctor_get(v_ictx_134_, 1);
lean_inc_ref(v_fileName_142_);
v_fileMap_143_ = lean_ctor_get(v_ictx_134_, 2);
lean_inc_ref_n(v_fileMap_143_, 2);
lean_dec_ref(v_ictx_134_);
v___x_144_ = l_Lean_FileMap_toPosition(v_fileMap_143_, v_fst_139_);
lean_dec(v_fst_139_);
if (lean_obj_tag(v_fst_140_) == 0)
{
lean_object* v___x_155_; 
lean_dec_ref(v_fileMap_143_);
v___x_155_ = lean_box(0);
v___y_146_ = v___x_155_;
goto v___jp_145_;
}
else
{
lean_object* v_val_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_val_156_ = lean_ctor_get(v_fst_140_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_fst_140_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v_fst_140_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_val_156_);
lean_dec(v_fst_140_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = l_Lean_FileMap_toPosition(v_fileMap_143_, v_val_156_);
lean_dec(v_val_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
v___y_146_ = v___x_162_;
goto v___jp_145_;
}
}
}
v___jp_145_:
{
uint8_t v___x_147_; uint8_t v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_147_ = 1;
v___x_148_ = 2;
v___x_149_ = 0;
v___x_150_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_151_ = l_Lean_Parser_Error_toString(v_snd_141_);
v___x_152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
v___x_153_ = l_Lean_MessageData_ofFormat(v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_154_, 0, v_fileName_142_);
lean_ctor_set(v___x_154_, 1, v___x_144_);
lean_ctor_set(v___x_154_, 2, v___y_146_);
lean_ctor_set(v___x_154_, 3, v___x_150_);
lean_ctor_set(v___x_154_, 4, v___x_153_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*5, v___x_147_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*5 + 1, v___x_148_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*5 + 2, v___x_149_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_parseErrors(lean_object* v_ictx_165_, lean_object* v_pmctx_166_, lean_object* v_tokens_167_, lean_object* v_input_168_, lean_object* v_ctxt_169_, lean_object* v_s_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
lean_inc_ref(v_s_170_);
v___x_171_ = l_Lean_Parser_ParserState_allErrors(v_s_170_);
v___x_172_ = lean_array_get_size(v___x_171_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_nat_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec_ref(v_s_170_);
lean_dec_ref(v_ctxt_169_);
lean_dec_ref(v_tokens_167_);
lean_dec_ref(v_pmctx_166_);
lean_dec_ref(v_ictx_165_);
return v___x_171_;
}
else
{
lean_object* v_pos_175_; uint8_t v___x_176_; 
v_pos_175_ = lean_ctor_get(v_s_170_, 2);
lean_inc(v_pos_175_);
lean_dec_ref(v_s_170_);
v___x_176_ = l_Lean_Parser_InputContext_atEnd(v_ictx_165_, v_pos_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec_ref(v___x_171_);
v___x_177_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_blockFn), 3, 1);
lean_closure_set(v___x_177_, 0, v_ctxt_169_);
v___x_178_ = l_Lean_Parser_mkParserState(v_input_168_);
v___x_179_ = l_Lean_Parser_ParserState_setPos(v___x_178_, v_pos_175_);
v___x_180_ = l_Lean_Parser_ParserFn_run(v___x_177_, v_ictx_165_, v_pmctx_166_, v_tokens_167_, v___x_179_);
v___x_181_ = l_Lean_Parser_ParserState_allErrors(v___x_180_);
return v___x_181_;
}
else
{
lean_dec(v_pos_175_);
lean_dec_ref(v_ctxt_169_);
lean_dec_ref(v_tokens_167_);
lean_dec_ref(v_pmctx_166_);
lean_dec_ref(v_ictx_165_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_parseErrors___boxed(lean_object* v_ictx_182_, lean_object* v_pmctx_183_, lean_object* v_tokens_184_, lean_object* v_input_185_, lean_object* v_ctxt_186_, lean_object* v_s_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v_ictx_182_, v_pmctx_183_, v_tokens_184_, v_input_185_, v_ctxt_186_, v_s_187_);
lean_dec_ref(v_input_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object* v_toPure_189_, lean_object* v_____r_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_box(0);
v___x_192_ = lean_apply_2(v_toPure_189_, lean_box(0), v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object* v_toPure_193_, lean_object* v_____s_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_box(0);
v___x_196_ = lean_apply_2(v_toPure_193_, lean_box(0), v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object* v___x_197_, lean_object* v_toPure_198_, lean_object* v_____r_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_197_);
v___x_201_ = lean_apply_2(v_toPure_198_, lean_box(0), v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object* v_ictx_202_, lean_object* v_logMessage_203_, lean_object* v_toBind_204_, lean_object* v___f_205_, lean_object* v_a_206_, lean_object* v_x_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_snd_209_; lean_object* v_fst_210_; lean_object* v_snd_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_snd_209_ = lean_ctor_get(v_a_206_, 1);
lean_inc(v_snd_209_);
v_fst_210_ = lean_ctor_get(v_a_206_, 0);
lean_inc(v_fst_210_);
lean_dec_ref(v_a_206_);
v_snd_211_ = lean_ctor_get(v_snd_209_, 1);
lean_inc(v_snd_211_);
lean_dec(v_snd_209_);
v___x_212_ = l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(v_ictx_202_, v_fst_210_, v_snd_211_);
v___x_213_ = lean_apply_1(v_logMessage_203_, v___x_212_);
v___x_214_ = lean_apply_4(v_toBind_204_, lean_box(0), lean_box(0), v___x_213_, v___f_205_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object* v_text_217_, lean_object* v_pos_218_, lean_object* v_source_219_, uint8_t v___x_220_, lean_object* v_logMessage_221_, lean_object* v_toBind_222_, lean_object* v___f_223_, lean_object* v_____do__lift_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint32_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_225_ = l_Lean_FileMap_toPosition(v_text_217_, v_pos_218_);
v___x_226_ = lean_box(0);
v___x_227_ = 2;
v___x_228_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_229_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__0));
v___x_230_ = lean_string_utf8_get(v_source_219_, v_pos_218_);
v___x_231_ = lean_string_push(v___x_228_, v___x_230_);
v___x_232_ = lean_string_append(v___x_229_, v___x_231_);
lean_dec_ref(v___x_231_);
v___x_233_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__1));
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
v___x_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = l_Lean_MessageData_ofFormat(v___x_235_);
v___x_237_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_237_, 0, v_____do__lift_224_);
lean_ctor_set(v___x_237_, 1, v___x_225_);
lean_ctor_set(v___x_237_, 2, v___x_226_);
lean_ctor_set(v___x_237_, 3, v___x_228_);
lean_ctor_set(v___x_237_, 4, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*5, v___x_220_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*5 + 1, v___x_227_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*5 + 2, v___x_220_);
v___x_238_ = lean_apply_1(v_logMessage_221_, v___x_237_);
v___x_239_ = lean_apply_4(v_toBind_222_, lean_box(0), lean_box(0), v___x_238_, v___f_223_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object* v_text_240_, lean_object* v_pos_241_, lean_object* v_source_242_, lean_object* v___x_243_, lean_object* v_logMessage_244_, lean_object* v_toBind_245_, lean_object* v___f_246_, lean_object* v_____do__lift_247_){
_start:
{
uint8_t v___x_1023__boxed_248_; lean_object* v_res_249_; 
v___x_1023__boxed_248_ = lean_unbox(v___x_243_);
v_res_249_ = l_Lean_parseVersoDocString___redArg___lam__4(v_text_240_, v_pos_241_, v_source_242_, v___x_1023__boxed_248_, v_logMessage_244_, v_toBind_245_, v___f_246_, v_____do__lift_247_);
lean_dec_ref(v_source_242_);
lean_dec(v_pos_241_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object* v_env_250_, lean_object* v_____do__lift_251_, lean_object* v_____do__lift_252_, lean_object* v_text_253_, lean_object* v_val_254_, lean_object* v___y_255_, lean_object* v_source_256_, lean_object* v_ictx_257_, lean_object* v_toPure_258_, lean_object* v_logMessage_259_, lean_object* v_toBind_260_, lean_object* v_inst_261_, lean_object* v___f_262_, lean_object* v___f_263_, lean_object* v_getFileName_264_, lean_object* v_____do__lift_265_){
_start:
{
lean_object* v_pmctx_266_; lean_object* v_blockCtxt_267_; lean_object* v___x_268_; lean_object* v_s_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_s_272_; lean_object* v_errors_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
lean_inc_ref(v_env_250_);
v_pmctx_266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_266_, 0, v_env_250_);
lean_ctor_set(v_pmctx_266_, 1, v_____do__lift_251_);
lean_ctor_set(v_pmctx_266_, 2, v_____do__lift_252_);
lean_ctor_set(v_pmctx_266_, 3, v_____do__lift_265_);
lean_inc(v_val_254_);
lean_inc_ref(v_text_253_);
v_blockCtxt_267_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_253_, v_val_254_, v___y_255_);
v___x_268_ = l_Lean_Parser_mkParserState(v_source_256_);
v_s_269_ = l_Lean_Parser_ParserState_setPos(v___x_268_, v_val_254_);
lean_inc_ref(v_blockCtxt_267_);
v___x_270_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_270_, 0, v_blockCtxt_267_);
v___x_271_ = l_Lean_Parser_getTokenTable(v_env_250_);
lean_inc_ref(v___x_271_);
lean_inc_ref(v_pmctx_266_);
lean_inc_ref_n(v_ictx_257_, 2);
v_s_272_ = l_Lean_Parser_ParserFn_run(v___x_270_, v_ictx_257_, v_pmctx_266_, v___x_271_, v_s_269_);
lean_inc_ref(v_s_272_);
v_errors_273_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v_ictx_257_, v_pmctx_266_, v___x_271_, v_source_256_, v_blockCtxt_267_, v_s_272_);
v___x_274_ = lean_array_get_size(v_errors_273_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_nat_dec_eq(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___f_278_; lean_object* v___f_279_; size_t v_sz_280_; size_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec_ref(v_s_272_);
lean_dec(v_getFileName_264_);
lean_dec(v___f_263_);
lean_dec_ref(v_source_256_);
lean_dec_ref(v_text_253_);
v___x_277_ = lean_box(0);
v___f_278_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_278_, 0, v___x_277_);
lean_closure_set(v___f_278_, 1, v_toPure_258_);
lean_inc(v_toBind_260_);
v___f_279_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3), 7, 4);
lean_closure_set(v___f_279_, 0, v_ictx_257_);
lean_closure_set(v___f_279_, 1, v_logMessage_259_);
lean_closure_set(v___f_279_, 2, v_toBind_260_);
lean_closure_set(v___f_279_, 3, v___f_278_);
v_sz_280_ = lean_array_size(v_errors_273_);
v___x_281_ = ((size_t)0ULL);
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_261_, v_errors_273_, v___f_279_, v_sz_280_, v___x_281_, v___x_277_);
v___x_283_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_282_, v___f_262_);
return v___x_283_;
}
else
{
lean_object* v_stxStack_284_; lean_object* v_pos_285_; uint8_t v___x_286_; 
lean_dec_ref(v_errors_273_);
lean_dec(v___f_262_);
lean_dec_ref(v_inst_261_);
v_stxStack_284_ = lean_ctor_get(v_s_272_, 0);
lean_inc_ref(v_stxStack_284_);
v_pos_285_ = lean_ctor_get(v_s_272_, 2);
lean_inc(v_pos_285_);
lean_dec_ref(v_s_272_);
v___x_286_ = l_Lean_Parser_InputContext_atEnd(v_ictx_257_, v_pos_285_);
lean_dec_ref(v_ictx_257_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___f_288_; lean_object* v___x_289_; 
lean_dec_ref(v_stxStack_284_);
lean_dec(v_toPure_258_);
v___x_287_ = lean_box(v___x_286_);
lean_inc(v_toBind_260_);
v___f_288_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_288_, 0, v_text_253_);
lean_closure_set(v___f_288_, 1, v_pos_285_);
lean_closure_set(v___f_288_, 2, v_source_256_);
lean_closure_set(v___f_288_, 3, v___x_287_);
lean_closure_set(v___f_288_, 4, v_logMessage_259_);
lean_closure_set(v___f_288_, 5, v_toBind_260_);
lean_closure_set(v___f_288_, 6, v___f_263_);
v___x_289_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v_getFileName_264_, v___f_288_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_pos_285_);
lean_dec(v_getFileName_264_);
lean_dec(v___f_263_);
lean_dec(v_toBind_260_);
lean_dec(v_logMessage_259_);
lean_dec_ref(v_source_256_);
lean_dec_ref(v_text_253_);
v___x_290_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_284_);
lean_dec_ref(v_stxStack_284_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_apply_2(v_toPure_258_, lean_box(0), v___x_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object* v_env_293_, lean_object* v_____do__lift_294_, lean_object* v_text_295_, lean_object* v_val_296_, lean_object* v___y_297_, lean_object* v_source_298_, lean_object* v_ictx_299_, lean_object* v_toPure_300_, lean_object* v_logMessage_301_, lean_object* v_toBind_302_, lean_object* v_inst_303_, lean_object* v___f_304_, lean_object* v___f_305_, lean_object* v_getFileName_306_, lean_object* v_getOpenDecls_307_, lean_object* v_____do__lift_308_){
_start:
{
lean_object* v___f_309_; lean_object* v___x_310_; 
lean_inc(v_toBind_302_);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__5), 16, 15);
lean_closure_set(v___f_309_, 0, v_env_293_);
lean_closure_set(v___f_309_, 1, v_____do__lift_294_);
lean_closure_set(v___f_309_, 2, v_____do__lift_308_);
lean_closure_set(v___f_309_, 3, v_text_295_);
lean_closure_set(v___f_309_, 4, v_val_296_);
lean_closure_set(v___f_309_, 5, v___y_297_);
lean_closure_set(v___f_309_, 6, v_source_298_);
lean_closure_set(v___f_309_, 7, v_ictx_299_);
lean_closure_set(v___f_309_, 8, v_toPure_300_);
lean_closure_set(v___f_309_, 9, v_logMessage_301_);
lean_closure_set(v___f_309_, 10, v_toBind_302_);
lean_closure_set(v___f_309_, 11, v_inst_303_);
lean_closure_set(v___f_309_, 12, v___f_304_);
lean_closure_set(v___f_309_, 13, v___f_305_);
lean_closure_set(v___f_309_, 14, v_getFileName_306_);
v___x_310_ = lean_apply_4(v_toBind_302_, lean_box(0), lean_box(0), v_getOpenDecls_307_, v___f_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object* v_inst_311_, lean_object* v_env_312_, lean_object* v_text_313_, lean_object* v_val_314_, lean_object* v___y_315_, lean_object* v_source_316_, lean_object* v_ictx_317_, lean_object* v_toPure_318_, lean_object* v_logMessage_319_, lean_object* v_toBind_320_, lean_object* v_inst_321_, lean_object* v___f_322_, lean_object* v___f_323_, lean_object* v_getFileName_324_, lean_object* v_____do__lift_325_){
_start:
{
lean_object* v_getCurrNamespace_326_; lean_object* v_getOpenDecls_327_; lean_object* v___f_328_; lean_object* v___x_329_; 
v_getCurrNamespace_326_ = lean_ctor_get(v_inst_311_, 0);
lean_inc(v_getCurrNamespace_326_);
v_getOpenDecls_327_ = lean_ctor_get(v_inst_311_, 1);
lean_inc(v_getOpenDecls_327_);
lean_dec_ref(v_inst_311_);
lean_inc(v_toBind_320_);
v___f_328_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__6), 16, 15);
lean_closure_set(v___f_328_, 0, v_env_312_);
lean_closure_set(v___f_328_, 1, v_____do__lift_325_);
lean_closure_set(v___f_328_, 2, v_text_313_);
lean_closure_set(v___f_328_, 3, v_val_314_);
lean_closure_set(v___f_328_, 4, v___y_315_);
lean_closure_set(v___f_328_, 5, v_source_316_);
lean_closure_set(v___f_328_, 6, v_ictx_317_);
lean_closure_set(v___f_328_, 7, v_toPure_318_);
lean_closure_set(v___f_328_, 8, v_logMessage_319_);
lean_closure_set(v___f_328_, 9, v_toBind_320_);
lean_closure_set(v___f_328_, 10, v_inst_321_);
lean_closure_set(v___f_328_, 11, v___f_322_);
lean_closure_set(v___f_328_, 12, v___f_323_);
lean_closure_set(v___f_328_, 13, v_getFileName_324_);
lean_closure_set(v___f_328_, 14, v_getOpenDecls_327_);
v___x_329_ = lean_apply_4(v_toBind_320_, lean_box(0), lean_box(0), v_getCurrNamespace_326_, v___f_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object* v_source_330_, lean_object* v_text_331_, lean_object* v___y_332_, lean_object* v_inst_333_, lean_object* v_env_334_, lean_object* v_val_335_, lean_object* v_toPure_336_, lean_object* v_logMessage_337_, lean_object* v_toBind_338_, lean_object* v_inst_339_, lean_object* v___f_340_, lean_object* v___f_341_, lean_object* v_getFileName_342_, lean_object* v_inst_343_, lean_object* v_____do__lift_344_){
_start:
{
lean_object* v_ictx_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
lean_inc(v___y_332_);
lean_inc_ref(v_text_331_);
lean_inc_ref(v_source_330_);
v_ictx_345_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_345_, 0, v_source_330_);
lean_ctor_set(v_ictx_345_, 1, v_____do__lift_344_);
lean_ctor_set(v_ictx_345_, 2, v_text_331_);
lean_ctor_set(v_ictx_345_, 3, v___y_332_);
lean_inc(v_toBind_338_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__7), 15, 14);
lean_closure_set(v___f_346_, 0, v_inst_333_);
lean_closure_set(v___f_346_, 1, v_env_334_);
lean_closure_set(v___f_346_, 2, v_text_331_);
lean_closure_set(v___f_346_, 3, v_val_335_);
lean_closure_set(v___f_346_, 4, v___y_332_);
lean_closure_set(v___f_346_, 5, v_source_330_);
lean_closure_set(v___f_346_, 6, v_ictx_345_);
lean_closure_set(v___f_346_, 7, v_toPure_336_);
lean_closure_set(v___f_346_, 8, v_logMessage_337_);
lean_closure_set(v___f_346_, 9, v_toBind_338_);
lean_closure_set(v___f_346_, 10, v_inst_339_);
lean_closure_set(v___f_346_, 11, v___f_340_);
lean_closure_set(v___f_346_, 12, v___f_341_);
lean_closure_set(v___f_346_, 13, v_getFileName_342_);
v___x_347_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v_inst_343_, v___f_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object* v_inst_348_, lean_object* v_source_349_, lean_object* v_text_350_, lean_object* v___y_351_, lean_object* v_inst_352_, lean_object* v_val_353_, lean_object* v_toPure_354_, lean_object* v_toBind_355_, lean_object* v_inst_356_, lean_object* v___f_357_, lean_object* v___f_358_, lean_object* v_inst_359_, lean_object* v_env_360_){
_start:
{
lean_object* v_getFileName_361_; lean_object* v_logMessage_362_; lean_object* v___f_363_; lean_object* v___x_364_; 
v_getFileName_361_ = lean_ctor_get(v_inst_348_, 2);
lean_inc_n(v_getFileName_361_, 2);
v_logMessage_362_ = lean_ctor_get(v_inst_348_, 4);
lean_inc(v_logMessage_362_);
lean_dec_ref(v_inst_348_);
lean_inc(v_toBind_355_);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__8), 15, 14);
lean_closure_set(v___f_363_, 0, v_source_349_);
lean_closure_set(v___f_363_, 1, v_text_350_);
lean_closure_set(v___f_363_, 2, v___y_351_);
lean_closure_set(v___f_363_, 3, v_inst_352_);
lean_closure_set(v___f_363_, 4, v_env_360_);
lean_closure_set(v___f_363_, 5, v_val_353_);
lean_closure_set(v___f_363_, 6, v_toPure_354_);
lean_closure_set(v___f_363_, 7, v_logMessage_362_);
lean_closure_set(v___f_363_, 8, v_toBind_355_);
lean_closure_set(v___f_363_, 9, v_inst_356_);
lean_closure_set(v___f_363_, 10, v___f_357_);
lean_closure_set(v___f_363_, 11, v___f_358_);
lean_closure_set(v___f_363_, 12, v_getFileName_361_);
lean_closure_set(v___f_363_, 13, v_inst_359_);
v___x_364_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v_getFileName_361_, v___f_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_parseVersoDocString___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__10___closed__0));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object* v_docComment_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_toPure_372_, lean_object* v_toBind_373_, lean_object* v_inst_374_, lean_object* v___f_375_, lean_object* v___f_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_text_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = l_Lean_Syntax_getArg(v_docComment_368_, v___x_380_);
v___x_382_ = 1;
v___x_383_ = l_Lean_Syntax_getPos_x3f(v___x_381_, v___x_382_);
if (lean_obj_tag(v___x_383_) == 1)
{
lean_object* v_val_384_; lean_object* v___x_385_; 
v_val_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v___x_383_, 1);
v___x_385_ = l_Lean_Syntax_getTailPos_x3f(v___x_381_, v___x_382_);
lean_dec(v___x_381_);
if (lean_obj_tag(v___x_385_) == 1)
{
lean_object* v_val_386_; lean_object* v_source_387_; lean_object* v___y_389_; lean_object* v___x_393_; lean_object* v_endPos_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
lean_dec_ref(v_inst_378_);
lean_dec(v_docComment_368_);
v_val_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v___x_385_, 1);
v_source_387_ = lean_ctor_get(v_text_379_, 0);
lean_inc_ref(v_source_387_);
v___x_393_ = lean_string_utf8_prev(v_source_387_, v_val_386_);
lean_dec(v_val_386_);
v_endPos_394_ = lean_string_utf8_prev(v_source_387_, v___x_393_);
lean_dec(v___x_393_);
v___x_395_ = lean_string_utf8_byte_size(v_source_387_);
v___x_396_ = lean_nat_dec_le(v_endPos_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_dec(v_endPos_394_);
v___y_389_ = v___x_395_;
goto v___jp_388_;
}
else
{
v___y_389_ = v_endPos_394_;
goto v___jp_388_;
}
v___jp_388_:
{
lean_object* v_getEnv_390_; lean_object* v___f_391_; lean_object* v___x_392_; 
v_getEnv_390_ = lean_ctor_get(v_inst_369_, 0);
lean_inc(v_getEnv_390_);
lean_dec_ref(v_inst_369_);
lean_inc(v_toBind_373_);
v___f_391_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__9), 13, 12);
lean_closure_set(v___f_391_, 0, v_inst_370_);
lean_closure_set(v___f_391_, 1, v_source_387_);
lean_closure_set(v___f_391_, 2, v_text_379_);
lean_closure_set(v___f_391_, 3, v___y_389_);
lean_closure_set(v___f_391_, 4, v_inst_371_);
lean_closure_set(v___f_391_, 5, v_val_384_);
lean_closure_set(v___f_391_, 6, v_toPure_372_);
lean_closure_set(v___f_391_, 7, v_toBind_373_);
lean_closure_set(v___f_391_, 8, v_inst_374_);
lean_closure_set(v___f_391_, 9, v___f_375_);
lean_closure_set(v___f_391_, 10, v___f_376_);
lean_closure_set(v___f_391_, 11, v_inst_377_);
v___x_392_ = lean_apply_4(v_toBind_373_, lean_box(0), lean_box(0), v_getEnv_390_, v___f_391_);
return v___x_392_;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v___x_385_);
lean_dec(v_val_384_);
lean_dec_ref(v_text_379_);
lean_dec(v_inst_377_);
lean_dec(v___f_376_);
lean_dec(v___f_375_);
lean_dec(v_toBind_373_);
lean_dec(v_toPure_372_);
lean_dec_ref(v_inst_371_);
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
v___x_397_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__10___closed__1, &l_Lean_parseVersoDocString___redArg___lam__10___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__10___closed__1);
v___x_398_ = l_Lean_throwErrorAt___redArg(v_inst_374_, v_inst_378_, v_docComment_368_, v___x_397_);
return v___x_398_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v___x_383_);
lean_dec(v___x_381_);
lean_dec_ref(v_text_379_);
lean_dec(v_inst_377_);
lean_dec(v___f_376_);
lean_dec(v___f_375_);
lean_dec(v_toBind_373_);
lean_dec(v_toPure_372_);
lean_dec_ref(v_inst_371_);
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
v___x_399_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__10___closed__1, &l_Lean_parseVersoDocString___redArg___lam__10___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__10___closed__1);
v___x_400_ = l_Lean_throwErrorAt___redArg(v_inst_374_, v_inst_378_, v_docComment_368_, v___x_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_docComment_408_){
_start:
{
lean_object* v_toApplicative_409_; lean_object* v_toBind_410_; lean_object* v_toPure_411_; lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
v_toApplicative_409_ = lean_ctor_get(v_inst_401_, 0);
v_toBind_410_ = lean_ctor_get(v_inst_401_, 1);
lean_inc_n(v_toBind_410_, 2);
v_toPure_411_ = lean_ctor_get(v_toApplicative_409_, 1);
lean_inc_n(v_toPure_411_, 3);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__0), 2, 1);
lean_closure_set(v___f_412_, 0, v_toPure_411_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__1), 2, 1);
lean_closure_set(v___f_413_, 0, v_toPure_411_);
v___f_414_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__10), 12, 11);
lean_closure_set(v___f_414_, 0, v_docComment_408_);
lean_closure_set(v___f_414_, 1, v_inst_404_);
lean_closure_set(v___f_414_, 2, v_inst_406_);
lean_closure_set(v___f_414_, 3, v_inst_407_);
lean_closure_set(v___f_414_, 4, v_toPure_411_);
lean_closure_set(v___f_414_, 5, v_toBind_410_);
lean_closure_set(v___f_414_, 6, v_inst_401_);
lean_closure_set(v___f_414_, 7, v___f_413_);
lean_closure_set(v___f_414_, 8, v___f_412_);
lean_closure_set(v___f_414_, 9, v_inst_405_);
lean_closure_set(v___f_414_, 10, v_inst_403_);
v___x_415_ = lean_apply_4(v_toBind_410_, lean_box(0), lean_box(0), v_inst_402_, v___f_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_m_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_docComment_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_parseVersoDocString___redArg(v_inst_417_, v_inst_418_, v_inst_419_, v_inst_420_, v_inst_421_, v_inst_422_, v_inst_423_, v_docComment_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorIdx(lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_unsigned_to_nat(0u);
return v___x_427_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(1u);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorIdx___boxed(lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_VersoDocstringView_ctorIdx(v_x_429_);
lean_dec_ref(v_x_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorElim___redArg(lean_object* v_t_431_, lean_object* v_k_432_){
_start:
{
lean_object* v_doc_433_; lean_object* v___x_434_; 
v_doc_433_ = lean_ctor_get(v_t_431_, 0);
lean_inc(v_doc_433_);
lean_dec_ref(v_t_431_);
v___x_434_ = lean_apply_1(v_k_432_, v_doc_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorElim(lean_object* v_motive_435_, lean_object* v_ctorIdx_436_, lean_object* v_t_437_, lean_object* v_h_438_, lean_object* v_k_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_VersoDocstringView_ctorElim___redArg(v_t_437_, v_k_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_ctorElim___boxed(lean_object* v_motive_441_, lean_object* v_ctorIdx_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_k_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_VersoDocstringView_ctorElim(v_motive_441_, v_ctorIdx_442_, v_t_443_, v_h_444_, v_k_445_);
lean_dec(v_ctorIdx_442_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_document_elim___redArg(lean_object* v_t_447_, lean_object* v_document_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_VersoDocstringView_ctorElim___redArg(v_t_447_, v_document_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_document_elim(lean_object* v_motive_450_, lean_object* v_t_451_, lean_object* v_h_452_, lean_object* v_document_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_VersoDocstringView_ctorElim___redArg(v_t_451_, v_document_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_parseFailure_elim___redArg(lean_object* v_t_455_, lean_object* v_parseFailure_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_VersoDocstringView_ctorElim___redArg(v_t_455_, v_parseFailure_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_parseFailure_elim(lean_object* v_motive_458_, lean_object* v_t_459_, lean_object* v_h_460_, lean_object* v_parseFailure_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_VersoDocstringView_ctorElim___redArg(v_t_459_, v_parseFailure_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of(lean_object* v_body_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = l_Lean_Syntax_getArg(v_body_472_, v___x_473_);
v___x_475_ = ((lean_object*)(l_Lean_VersoDocstringView_of___closed__4));
lean_inc(v___x_474_);
v___x_476_ = l_Lean_Syntax_isOfKind(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_474_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = l_Lean_Syntax_getArg(v___x_474_, v___x_473_);
lean_dec(v___x_474_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of___boxed(lean_object* v_body_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_VersoDocstringView_of(v_body_480_);
lean_dec(v_body_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object* v_text_482_, lean_object* v_pos_483_, lean_object* v_source_484_, uint8_t v___x_485_, lean_object* v_logMessage_486_, lean_object* v_____do__lift_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint32_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_488_ = l_Lean_FileMap_toPosition(v_text_482_, v_pos_483_);
v___x_489_ = lean_box(0);
v___x_490_ = 2;
v___x_491_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_492_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__0));
v___x_493_ = lean_string_utf8_get(v_source_484_, v_pos_483_);
v___x_494_ = lean_string_push(v___x_491_, v___x_493_);
v___x_495_ = lean_string_append(v___x_492_, v___x_494_);
lean_dec_ref(v___x_494_);
v___x_496_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__1));
v___x_497_ = lean_string_append(v___x_495_, v___x_496_);
v___x_498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
v___x_499_ = l_Lean_MessageData_ofFormat(v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_500_, 0, v_____do__lift_487_);
lean_ctor_set(v___x_500_, 1, v___x_488_);
lean_ctor_set(v___x_500_, 2, v___x_489_);
lean_ctor_set(v___x_500_, 3, v___x_491_);
lean_ctor_set(v___x_500_, 4, v___x_499_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*5, v___x_485_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*5 + 1, v___x_490_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*5 + 2, v___x_485_);
v___x_501_ = lean_apply_1(v_logMessage_486_, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object* v_text_502_, lean_object* v_pos_503_, lean_object* v_source_504_, lean_object* v___x_505_, lean_object* v_logMessage_506_, lean_object* v_____do__lift_507_){
_start:
{
uint8_t v___x_699__boxed_508_; lean_object* v_res_509_; 
v___x_699__boxed_508_ = lean_unbox(v___x_505_);
v_res_509_ = l_Lean_reportVersoParseFailure___redArg___lam__0(v_text_502_, v_pos_503_, v_source_504_, v___x_699__boxed_508_, v_logMessage_506_, v_____do__lift_507_);
lean_dec_ref(v_source_504_);
lean_dec(v_pos_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object* v_toPure_510_, lean_object* v_errors_511_, lean_object* v_s_512_, lean_object* v_ictx_513_, lean_object* v_text_514_, lean_object* v_source_515_, lean_object* v_logMessage_516_, lean_object* v_toBind_517_, lean_object* v_getFileName_518_, lean_object* v_____s_519_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_array_get_size(v_errors_511_);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_nat_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v_getFileName_518_);
lean_dec(v_toBind_517_);
lean_dec(v_logMessage_516_);
lean_dec_ref(v_source_515_);
lean_dec_ref(v_text_514_);
lean_dec_ref(v_s_512_);
goto v___jp_520_;
}
else
{
lean_object* v_pos_526_; uint8_t v___x_527_; 
v_pos_526_ = lean_ctor_get(v_s_512_, 2);
lean_inc(v_pos_526_);
lean_dec_ref(v_s_512_);
v___x_527_ = l_Lean_Parser_InputContext_atEnd(v_ictx_513_, v_pos_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___f_529_; lean_object* v___x_530_; 
lean_dec(v_toPure_510_);
v___x_528_ = lean_box(v___x_527_);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_529_, 0, v_text_514_);
lean_closure_set(v___f_529_, 1, v_pos_526_);
lean_closure_set(v___f_529_, 2, v_source_515_);
lean_closure_set(v___f_529_, 3, v___x_528_);
lean_closure_set(v___f_529_, 4, v_logMessage_516_);
v___x_530_ = lean_apply_4(v_toBind_517_, lean_box(0), lean_box(0), v_getFileName_518_, v___f_529_);
return v___x_530_;
}
else
{
lean_dec(v_pos_526_);
lean_dec(v_getFileName_518_);
lean_dec(v_toBind_517_);
lean_dec(v_logMessage_516_);
lean_dec_ref(v_source_515_);
lean_dec_ref(v_text_514_);
goto v___jp_520_;
}
}
v___jp_520_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_box(0);
v___x_522_ = lean_apply_2(v_toPure_510_, lean_box(0), v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object* v_toPure_531_, lean_object* v_errors_532_, lean_object* v_s_533_, lean_object* v_ictx_534_, lean_object* v_text_535_, lean_object* v_source_536_, lean_object* v_logMessage_537_, lean_object* v_toBind_538_, lean_object* v_getFileName_539_, lean_object* v_____s_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_reportVersoParseFailure___redArg___lam__1(v_toPure_531_, v_errors_532_, v_s_533_, v_ictx_534_, v_text_535_, v_source_536_, v_logMessage_537_, v_toBind_538_, v_getFileName_539_, v_____s_540_);
lean_dec_ref(v_ictx_534_);
lean_dec_ref(v_errors_532_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object* v_env_542_, lean_object* v_____do__lift_543_, lean_object* v_____do__lift_544_, lean_object* v_text_545_, lean_object* v_val_546_, lean_object* v___y_547_, lean_object* v_source_548_, lean_object* v_ictx_549_, lean_object* v_toPure_550_, lean_object* v_logMessage_551_, lean_object* v_toBind_552_, lean_object* v_getFileName_553_, lean_object* v_inst_554_, lean_object* v_____do__lift_555_){
_start:
{
lean_object* v_pmctx_556_; lean_object* v_blockCtxt_557_; lean_object* v___x_558_; lean_object* v_s_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_s_562_; lean_object* v_errors_563_; lean_object* v___f_564_; lean_object* v___x_565_; lean_object* v___f_566_; lean_object* v___f_567_; size_t v_sz_568_; size_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_inc_ref(v_env_542_);
v_pmctx_556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_556_, 0, v_env_542_);
lean_ctor_set(v_pmctx_556_, 1, v_____do__lift_543_);
lean_ctor_set(v_pmctx_556_, 2, v_____do__lift_544_);
lean_ctor_set(v_pmctx_556_, 3, v_____do__lift_555_);
lean_inc(v_val_546_);
lean_inc_ref(v_text_545_);
v_blockCtxt_557_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_545_, v_val_546_, v___y_547_);
v___x_558_ = l_Lean_Parser_mkParserState(v_source_548_);
v_s_559_ = l_Lean_Parser_ParserState_setPos(v___x_558_, v_val_546_);
lean_inc_ref(v_blockCtxt_557_);
v___x_560_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_560_, 0, v_blockCtxt_557_);
v___x_561_ = l_Lean_Parser_getTokenTable(v_env_542_);
lean_inc_ref(v___x_561_);
lean_inc_ref(v_pmctx_556_);
lean_inc_ref_n(v_ictx_549_, 3);
v_s_562_ = l_Lean_Parser_ParserFn_run(v___x_560_, v_ictx_549_, v_pmctx_556_, v___x_561_, v_s_559_);
lean_inc_ref(v_s_562_);
v_errors_563_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v_ictx_549_, v_pmctx_556_, v___x_561_, v_source_548_, v_blockCtxt_557_, v_s_562_);
lean_inc_n(v_toBind_552_, 2);
lean_inc(v_logMessage_551_);
lean_inc_ref(v_errors_563_);
lean_inc(v_toPure_550_);
v___f_564_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_564_, 0, v_toPure_550_);
lean_closure_set(v___f_564_, 1, v_errors_563_);
lean_closure_set(v___f_564_, 2, v_s_562_);
lean_closure_set(v___f_564_, 3, v_ictx_549_);
lean_closure_set(v___f_564_, 4, v_text_545_);
lean_closure_set(v___f_564_, 5, v_source_548_);
lean_closure_set(v___f_564_, 6, v_logMessage_551_);
lean_closure_set(v___f_564_, 7, v_toBind_552_);
lean_closure_set(v___f_564_, 8, v_getFileName_553_);
v___x_565_ = lean_box(0);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_566_, 0, v___x_565_);
lean_closure_set(v___f_566_, 1, v_toPure_550_);
v___f_567_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3), 7, 4);
lean_closure_set(v___f_567_, 0, v_ictx_549_);
lean_closure_set(v___f_567_, 1, v_logMessage_551_);
lean_closure_set(v___f_567_, 2, v_toBind_552_);
lean_closure_set(v___f_567_, 3, v___f_566_);
v_sz_568_ = lean_array_size(v_errors_563_);
v___x_569_ = ((size_t)0ULL);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_554_, v_errors_563_, v___f_567_, v_sz_568_, v___x_569_, v___x_565_);
v___x_571_ = lean_apply_4(v_toBind_552_, lean_box(0), lean_box(0), v___x_570_, v___f_564_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object* v_env_572_, lean_object* v_____do__lift_573_, lean_object* v_text_574_, lean_object* v_val_575_, lean_object* v___y_576_, lean_object* v_source_577_, lean_object* v_ictx_578_, lean_object* v_toPure_579_, lean_object* v_logMessage_580_, lean_object* v_toBind_581_, lean_object* v_getFileName_582_, lean_object* v_inst_583_, lean_object* v_getOpenDecls_584_, lean_object* v_____do__lift_585_){
_start:
{
lean_object* v___f_586_; lean_object* v___x_587_; 
lean_inc(v_toBind_581_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__4), 14, 13);
lean_closure_set(v___f_586_, 0, v_env_572_);
lean_closure_set(v___f_586_, 1, v_____do__lift_573_);
lean_closure_set(v___f_586_, 2, v_____do__lift_585_);
lean_closure_set(v___f_586_, 3, v_text_574_);
lean_closure_set(v___f_586_, 4, v_val_575_);
lean_closure_set(v___f_586_, 5, v___y_576_);
lean_closure_set(v___f_586_, 6, v_source_577_);
lean_closure_set(v___f_586_, 7, v_ictx_578_);
lean_closure_set(v___f_586_, 8, v_toPure_579_);
lean_closure_set(v___f_586_, 9, v_logMessage_580_);
lean_closure_set(v___f_586_, 10, v_toBind_581_);
lean_closure_set(v___f_586_, 11, v_getFileName_582_);
lean_closure_set(v___f_586_, 12, v_inst_583_);
v___x_587_ = lean_apply_4(v_toBind_581_, lean_box(0), lean_box(0), v_getOpenDecls_584_, v___f_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object* v_inst_588_, lean_object* v_env_589_, lean_object* v_text_590_, lean_object* v_val_591_, lean_object* v___y_592_, lean_object* v_source_593_, lean_object* v_ictx_594_, lean_object* v_toPure_595_, lean_object* v_logMessage_596_, lean_object* v_toBind_597_, lean_object* v_getFileName_598_, lean_object* v_inst_599_, lean_object* v_____do__lift_600_){
_start:
{
lean_object* v_getCurrNamespace_601_; lean_object* v_getOpenDecls_602_; lean_object* v___f_603_; lean_object* v___x_604_; 
v_getCurrNamespace_601_ = lean_ctor_get(v_inst_588_, 0);
lean_inc(v_getCurrNamespace_601_);
v_getOpenDecls_602_ = lean_ctor_get(v_inst_588_, 1);
lean_inc(v_getOpenDecls_602_);
lean_dec_ref(v_inst_588_);
lean_inc(v_toBind_597_);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__2), 14, 13);
lean_closure_set(v___f_603_, 0, v_env_589_);
lean_closure_set(v___f_603_, 1, v_____do__lift_600_);
lean_closure_set(v___f_603_, 2, v_text_590_);
lean_closure_set(v___f_603_, 3, v_val_591_);
lean_closure_set(v___f_603_, 4, v___y_592_);
lean_closure_set(v___f_603_, 5, v_source_593_);
lean_closure_set(v___f_603_, 6, v_ictx_594_);
lean_closure_set(v___f_603_, 7, v_toPure_595_);
lean_closure_set(v___f_603_, 8, v_logMessage_596_);
lean_closure_set(v___f_603_, 9, v_toBind_597_);
lean_closure_set(v___f_603_, 10, v_getFileName_598_);
lean_closure_set(v___f_603_, 11, v_inst_599_);
lean_closure_set(v___f_603_, 12, v_getOpenDecls_602_);
v___x_604_ = lean_apply_4(v_toBind_597_, lean_box(0), lean_box(0), v_getCurrNamespace_601_, v___f_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object* v_source_605_, lean_object* v_text_606_, lean_object* v___y_607_, lean_object* v_inst_608_, lean_object* v_env_609_, lean_object* v_val_610_, lean_object* v_toPure_611_, lean_object* v_logMessage_612_, lean_object* v_toBind_613_, lean_object* v_getFileName_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_____do__lift_617_){
_start:
{
lean_object* v_ictx_618_; lean_object* v___f_619_; lean_object* v___x_620_; 
lean_inc(v___y_607_);
lean_inc_ref(v_text_606_);
lean_inc_ref(v_source_605_);
v_ictx_618_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_618_, 0, v_source_605_);
lean_ctor_set(v_ictx_618_, 1, v_____do__lift_617_);
lean_ctor_set(v_ictx_618_, 2, v_text_606_);
lean_ctor_set(v_ictx_618_, 3, v___y_607_);
lean_inc(v_toBind_613_);
v___f_619_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__3), 13, 12);
lean_closure_set(v___f_619_, 0, v_inst_608_);
lean_closure_set(v___f_619_, 1, v_env_609_);
lean_closure_set(v___f_619_, 2, v_text_606_);
lean_closure_set(v___f_619_, 3, v_val_610_);
lean_closure_set(v___f_619_, 4, v___y_607_);
lean_closure_set(v___f_619_, 5, v_source_605_);
lean_closure_set(v___f_619_, 6, v_ictx_618_);
lean_closure_set(v___f_619_, 7, v_toPure_611_);
lean_closure_set(v___f_619_, 8, v_logMessage_612_);
lean_closure_set(v___f_619_, 9, v_toBind_613_);
lean_closure_set(v___f_619_, 10, v_getFileName_614_);
lean_closure_set(v___f_619_, 11, v_inst_615_);
v___x_620_ = lean_apply_4(v_toBind_613_, lean_box(0), lean_box(0), v_inst_616_, v___f_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object* v_inst_621_, lean_object* v_source_622_, lean_object* v_text_623_, lean_object* v___y_624_, lean_object* v_inst_625_, lean_object* v_val_626_, lean_object* v_toPure_627_, lean_object* v_toBind_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_env_631_){
_start:
{
lean_object* v_getFileName_632_; lean_object* v_logMessage_633_; lean_object* v___f_634_; lean_object* v___x_635_; 
v_getFileName_632_ = lean_ctor_get(v_inst_621_, 2);
lean_inc_n(v_getFileName_632_, 2);
v_logMessage_633_ = lean_ctor_get(v_inst_621_, 4);
lean_inc(v_logMessage_633_);
lean_dec_ref(v_inst_621_);
lean_inc(v_toBind_628_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__5), 13, 12);
lean_closure_set(v___f_634_, 0, v_source_622_);
lean_closure_set(v___f_634_, 1, v_text_623_);
lean_closure_set(v___f_634_, 2, v___y_624_);
lean_closure_set(v___f_634_, 3, v_inst_625_);
lean_closure_set(v___f_634_, 4, v_env_631_);
lean_closure_set(v___f_634_, 5, v_val_626_);
lean_closure_set(v___f_634_, 6, v_toPure_627_);
lean_closure_set(v___f_634_, 7, v_logMessage_633_);
lean_closure_set(v___f_634_, 8, v_toBind_628_);
lean_closure_set(v___f_634_, 9, v_getFileName_632_);
lean_closure_set(v___f_634_, 10, v_inst_629_);
lean_closure_set(v___f_634_, 11, v_inst_630_);
v___x_635_ = lean_apply_4(v_toBind_628_, lean_box(0), lean_box(0), v_getFileName_632_, v___f_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_val_639_, lean_object* v_toPure_640_, lean_object* v_toBind_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_val_644_, lean_object* v_text_645_){
_start:
{
lean_object* v_source_646_; lean_object* v___y_648_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_source_646_ = lean_ctor_get(v_text_645_, 0);
lean_inc_ref(v_source_646_);
v___x_652_ = lean_string_utf8_byte_size(v_source_646_);
v___x_653_ = lean_nat_dec_le(v_val_644_, v___x_652_);
if (v___x_653_ == 0)
{
lean_dec(v_val_644_);
v___y_648_ = v___x_652_;
goto v___jp_647_;
}
else
{
v___y_648_ = v_val_644_;
goto v___jp_647_;
}
v___jp_647_:
{
lean_object* v_getEnv_649_; lean_object* v___f_650_; lean_object* v___x_651_; 
v_getEnv_649_ = lean_ctor_get(v_inst_636_, 0);
lean_inc(v_getEnv_649_);
lean_dec_ref(v_inst_636_);
lean_inc(v_toBind_641_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__6), 11, 10);
lean_closure_set(v___f_650_, 0, v_inst_637_);
lean_closure_set(v___f_650_, 1, v_source_646_);
lean_closure_set(v___f_650_, 2, v_text_645_);
lean_closure_set(v___f_650_, 3, v___y_648_);
lean_closure_set(v___f_650_, 4, v_inst_638_);
lean_closure_set(v___f_650_, 5, v_val_639_);
lean_closure_set(v___f_650_, 6, v_toPure_640_);
lean_closure_set(v___f_650_, 7, v_toBind_641_);
lean_closure_set(v___f_650_, 8, v_inst_642_);
lean_closure_set(v___f_650_, 9, v_inst_643_);
v___x_651_ = lean_apply_4(v_toBind_641_, lean_box(0), lean_box(0), v_getEnv_649_, v___f_650_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_rawAtom_660_){
_start:
{
lean_object* v_toApplicative_661_; lean_object* v_toBind_662_; lean_object* v_toPure_663_; uint8_t v___x_664_; lean_object* v___x_665_; 
v_toApplicative_661_ = lean_ctor_get(v_inst_654_, 0);
v_toBind_662_ = lean_ctor_get(v_inst_654_, 1);
lean_inc(v_toBind_662_);
v_toPure_663_ = lean_ctor_get(v_toApplicative_661_, 1);
lean_inc(v_toPure_663_);
v___x_664_ = 1;
v___x_665_ = l_Lean_Syntax_getPos_x3f(v_rawAtom_660_, v___x_664_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v_val_666_; lean_object* v___x_667_; 
v_val_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l_Lean_Syntax_getTailPos_x3f(v_rawAtom_660_, v___x_664_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___f_669_; lean_object* v___x_670_; 
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
lean_inc(v_toBind_662_);
v___f_669_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__7), 10, 9);
lean_closure_set(v___f_669_, 0, v_inst_656_);
lean_closure_set(v___f_669_, 1, v_inst_658_);
lean_closure_set(v___f_669_, 2, v_inst_659_);
lean_closure_set(v___f_669_, 3, v_val_666_);
lean_closure_set(v___f_669_, 4, v_toPure_663_);
lean_closure_set(v___f_669_, 5, v_toBind_662_);
lean_closure_set(v___f_669_, 6, v_inst_654_);
lean_closure_set(v___f_669_, 7, v_inst_657_);
lean_closure_set(v___f_669_, 8, v_val_668_);
v___x_670_ = lean_apply_4(v_toBind_662_, lean_box(0), lean_box(0), v_inst_655_, v___f_669_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v___x_667_);
lean_dec(v_val_666_);
lean_dec(v_toBind_662_);
lean_dec_ref(v_inst_659_);
lean_dec_ref(v_inst_658_);
lean_dec(v_inst_657_);
lean_dec_ref(v_inst_656_);
lean_dec(v_inst_655_);
lean_dec_ref(v_inst_654_);
v___x_671_ = lean_box(0);
v___x_672_ = lean_apply_2(v_toPure_663_, lean_box(0), v___x_671_);
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v___x_665_);
lean_dec(v_toBind_662_);
lean_dec_ref(v_inst_659_);
lean_dec_ref(v_inst_658_);
lean_dec(v_inst_657_);
lean_dec_ref(v_inst_656_);
lean_dec(v_inst_655_);
lean_dec_ref(v_inst_654_);
v___x_673_ = lean_box(0);
v___x_674_ = lean_apply_2(v_toPure_663_, lean_box(0), v___x_673_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_rawAtom_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_reportVersoParseFailure___redArg(v_inst_675_, v_inst_676_, v_inst_677_, v_inst_678_, v_inst_679_, v_inst_680_, v_rawAtom_681_);
lean_dec(v_rawAtom_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_m_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_rawAtom_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_reportVersoParseFailure___redArg(v_inst_684_, v_inst_685_, v_inst_687_, v_inst_688_, v_inst_689_, v_inst_690_, v_rawAtom_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_m_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_rawAtom_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_reportVersoParseFailure(v_m_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_inst_697_, v_inst_698_, v_inst_699_, v_inst_700_, v_rawAtom_701_);
lean_dec(v_rawAtom_701_);
lean_dec_ref(v_inst_696_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_703_, lean_object* v_declName_704_, lean_object* v_binders_705_, lean_object* v___x_706_, uint8_t v___x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_703_) == 0)
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Doc_DocM_exec___redArg(v_declName_704_, v_binders_705_, v___x_706_, v___x_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_715_;
}
else
{
lean_object* v_toCold_716_; lean_object* v_val_717_; lean_object* v_currRecDepth_718_; lean_object* v_ref_719_; uint8_t v_diag_720_; uint8_t v_suppressElabErrors_721_; lean_object* v_fileName_722_; lean_object* v_options_723_; lean_object* v_maxRecDepth_724_; lean_object* v_currNamespace_725_; lean_object* v_openDecls_726_; lean_object* v_initHeartbeats_727_; lean_object* v_maxHeartbeats_728_; lean_object* v_quotContext_729_; lean_object* v_currMacroScope_730_; lean_object* v_cancelTk_x3f_731_; lean_object* v_inheritedTraceOptions_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_toCold_716_ = lean_ctor_get(v___y_712_, 0);
v_val_717_ = lean_ctor_get(v_fileMap_x3f_703_, 0);
v_currRecDepth_718_ = lean_ctor_get(v___y_712_, 1);
v_ref_719_ = lean_ctor_get(v___y_712_, 2);
v_diag_720_ = lean_ctor_get_uint8(v___y_712_, sizeof(void*)*3);
v_suppressElabErrors_721_ = lean_ctor_get_uint8(v___y_712_, sizeof(void*)*3 + 1);
v_fileName_722_ = lean_ctor_get(v_toCold_716_, 0);
v_options_723_ = lean_ctor_get(v_toCold_716_, 2);
v_maxRecDepth_724_ = lean_ctor_get(v_toCold_716_, 3);
v_currNamespace_725_ = lean_ctor_get(v_toCold_716_, 4);
v_openDecls_726_ = lean_ctor_get(v_toCold_716_, 5);
v_initHeartbeats_727_ = lean_ctor_get(v_toCold_716_, 6);
v_maxHeartbeats_728_ = lean_ctor_get(v_toCold_716_, 7);
v_quotContext_729_ = lean_ctor_get(v_toCold_716_, 8);
v_currMacroScope_730_ = lean_ctor_get(v_toCold_716_, 9);
v_cancelTk_x3f_731_ = lean_ctor_get(v_toCold_716_, 10);
v_inheritedTraceOptions_732_ = lean_ctor_get(v_toCold_716_, 11);
lean_inc_ref(v_inheritedTraceOptions_732_);
lean_inc(v_cancelTk_x3f_731_);
lean_inc(v_currMacroScope_730_);
lean_inc(v_quotContext_729_);
lean_inc(v_maxHeartbeats_728_);
lean_inc(v_initHeartbeats_727_);
lean_inc(v_openDecls_726_);
lean_inc(v_currNamespace_725_);
lean_inc(v_maxRecDepth_724_);
lean_inc_ref(v_options_723_);
lean_inc(v_val_717_);
lean_inc_ref(v_fileName_722_);
v___x_733_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_733_, 0, v_fileName_722_);
lean_ctor_set(v___x_733_, 1, v_val_717_);
lean_ctor_set(v___x_733_, 2, v_options_723_);
lean_ctor_set(v___x_733_, 3, v_maxRecDepth_724_);
lean_ctor_set(v___x_733_, 4, v_currNamespace_725_);
lean_ctor_set(v___x_733_, 5, v_openDecls_726_);
lean_ctor_set(v___x_733_, 6, v_initHeartbeats_727_);
lean_ctor_set(v___x_733_, 7, v_maxHeartbeats_728_);
lean_ctor_set(v___x_733_, 8, v_quotContext_729_);
lean_ctor_set(v___x_733_, 9, v_currMacroScope_730_);
lean_ctor_set(v___x_733_, 10, v_cancelTk_x3f_731_);
lean_ctor_set(v___x_733_, 11, v_inheritedTraceOptions_732_);
lean_inc(v_ref_719_);
lean_inc(v_currRecDepth_718_);
v___x_734_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v_currRecDepth_718_);
lean_ctor_set(v___x_734_, 2, v_ref_719_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*3, v_diag_720_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*3 + 1, v_suppressElabErrors_721_);
v___x_735_ = l_Lean_Doc_DocM_exec___redArg(v_declName_704_, v_binders_705_, v___x_706_, v___x_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___x_734_, v___y_713_);
lean_dec_ref_known(v___x_734_, 3);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_736_, lean_object* v_declName_737_, lean_object* v_binders_738_, lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_9756__boxed_748_; lean_object* v_res_749_; 
v___x_9756__boxed_748_ = lean_unbox(v___x_740_);
v_res_749_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_736_, v_declName_737_, v_binders_738_, v___x_739_, v___x_9756__boxed_748_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_fileMap_x3f_736_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_750_, size_t v_i_751_, lean_object* v_bs_752_){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = lean_usize_dec_lt(v_i_751_, v_sz_750_);
if (v___x_753_ == 0)
{
return v_bs_752_;
}
else
{
lean_object* v_v_754_; lean_object* v___x_755_; lean_object* v_bs_x27_756_; size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; 
v_v_754_ = lean_array_uget(v_bs_752_, v_i_751_);
v___x_755_ = lean_unsigned_to_nat(0u);
v_bs_x27_756_ = lean_array_uset(v_bs_752_, v_i_751_, v___x_755_);
v___x_757_ = ((size_t)1ULL);
v___x_758_ = lean_usize_add(v_i_751_, v___x_757_);
v___x_759_ = lean_array_uset(v_bs_x27_756_, v_i_751_, v_v_754_);
v_i_751_ = v___x_758_;
v_bs_752_ = v___x_759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_761_, lean_object* v_i_762_, lean_object* v_bs_763_){
_start:
{
size_t v_sz_boxed_764_; size_t v_i_boxed_765_; lean_object* v_res_766_; 
v_sz_boxed_764_ = lean_unbox_usize(v_sz_761_);
lean_dec(v_sz_761_);
v_i_boxed_765_ = lean_unbox_usize(v_i_762_);
lean_dec(v_i_762_);
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_764_, v_i_boxed_765_, v_bs_763_);
return v_res_766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_767_, lean_object* v_opt_768_){
_start:
{
lean_object* v_name_769_; lean_object* v_defValue_770_; lean_object* v_map_771_; lean_object* v___x_772_; 
v_name_769_ = lean_ctor_get(v_opt_768_, 0);
v_defValue_770_ = lean_ctor_get(v_opt_768_, 1);
v_map_771_ = lean_ctor_get(v_opts_767_, 0);
v___x_772_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_771_, v_name_769_);
if (lean_obj_tag(v___x_772_) == 0)
{
uint8_t v___x_773_; 
v___x_773_ = lean_unbox(v_defValue_770_);
return v___x_773_;
}
else
{
lean_object* v_val_774_; 
v_val_774_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_val_774_);
lean_dec_ref_known(v___x_772_, 1);
if (lean_obj_tag(v_val_774_) == 1)
{
uint8_t v_v_775_; 
v_v_775_ = lean_ctor_get_uint8(v_val_774_, 0);
lean_dec_ref_known(v_val_774_, 0);
return v_v_775_;
}
else
{
uint8_t v___x_776_; 
lean_dec(v_val_774_);
v___x_776_ = lean_unbox(v_defValue_770_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_777_, lean_object* v_opt_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_777_, v_opt_778_);
lean_dec_ref(v_opt_778_);
lean_dec_ref(v_opts_777_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v_env_788_; lean_object* v___x_789_; lean_object* v_toCold_790_; lean_object* v_mctx_791_; lean_object* v_lctx_792_; lean_object* v_options_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_787_ = lean_st_ref_get(v___y_785_);
v_env_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_ref(v_env_788_);
lean_dec(v___x_787_);
v___x_789_ = lean_st_ref_get(v___y_783_);
v_toCold_790_ = lean_ctor_get(v___y_784_, 0);
v_mctx_791_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_mctx_791_);
lean_dec(v___x_789_);
v_lctx_792_ = lean_ctor_get(v___y_782_, 2);
v_options_793_ = lean_ctor_get(v_toCold_790_, 2);
lean_inc_ref(v_options_793_);
lean_inc_ref(v_lctx_792_);
v___x_794_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_794_, 0, v_env_788_);
lean_ctor_set(v___x_794_, 1, v_mctx_791_);
lean_ctor_set(v___x_794_, 2, v_lctx_792_);
lean_ctor_set(v___x_794_, 3, v_options_793_);
v___x_795_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v_msgData_781_);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_812_, uint8_t v___y_813_, lean_object* v_x_814_){
_start:
{
if (lean_obj_tag(v_x_814_) == 1)
{
lean_object* v_pre_815_; 
v_pre_815_ = lean_ctor_get(v_x_814_, 0);
switch(lean_obj_tag(v_pre_815_))
{
case 1:
{
lean_object* v_pre_816_; 
v_pre_816_ = lean_ctor_get(v_pre_815_, 0);
switch(lean_obj_tag(v_pre_816_))
{
case 0:
{
lean_object* v_str_817_; lean_object* v_str_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_str_817_ = lean_ctor_get(v_x_814_, 1);
v_str_818_ = lean_ctor_get(v_pre_815_, 1);
v___x_819_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_820_ = lean_string_dec_eq(v_str_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_822_ = lean_string_dec_eq(v_str_818_, v___x_821_);
if (v___x_822_ == 0)
{
return v___x_822_;
}
else
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_824_ = lean_string_dec_eq(v_str_817_, v___x_823_);
if (v___x_824_ == 0)
{
return v___x_824_;
}
else
{
return v_suppressElabErrors_812_;
}
}
}
else
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_826_ = lean_string_dec_eq(v_str_817_, v___x_825_);
if (v___x_826_ == 0)
{
return v___x_826_;
}
else
{
return v_suppressElabErrors_812_;
}
}
}
case 1:
{
lean_object* v_pre_827_; 
v_pre_827_ = lean_ctor_get(v_pre_816_, 0);
if (lean_obj_tag(v_pre_827_) == 0)
{
lean_object* v_str_828_; lean_object* v_str_829_; lean_object* v_str_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_str_828_ = lean_ctor_get(v_x_814_, 1);
v_str_829_ = lean_ctor_get(v_pre_815_, 1);
v_str_830_ = lean_ctor_get(v_pre_816_, 1);
v___x_831_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_832_ = lean_string_dec_eq(v_str_830_, v___x_831_);
if (v___x_832_ == 0)
{
return v___x_832_;
}
else
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_834_ = lean_string_dec_eq(v_str_829_, v___x_833_);
if (v___x_834_ == 0)
{
return v___x_834_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_836_ = lean_string_dec_eq(v_str_828_, v___x_835_);
if (v___x_836_ == 0)
{
return v___x_836_;
}
else
{
return v_suppressElabErrors_812_;
}
}
}
}
else
{
return v___y_813_;
}
}
default: 
{
return v___y_813_;
}
}
}
case 0:
{
lean_object* v_str_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_str_837_ = lean_ctor_get(v_x_814_, 1);
v___x_838_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_839_ = lean_string_dec_eq(v_str_837_, v___x_838_);
if (v___x_839_ == 0)
{
return v___x_839_;
}
else
{
return v_suppressElabErrors_812_;
}
}
default: 
{
return v___y_813_;
}
}
}
else
{
return v___y_813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_840_, lean_object* v___y_841_, lean_object* v_x_842_){
_start:
{
uint8_t v_suppressElabErrors_boxed_843_; uint8_t v___y_9855__boxed_844_; uint8_t v_res_845_; lean_object* v_r_846_; 
v_suppressElabErrors_boxed_843_ = lean_unbox(v_suppressElabErrors_840_);
v___y_9855__boxed_844_ = lean_unbox(v___y_841_);
v_res_845_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_843_, v___y_9855__boxed_844_, v_x_842_);
lean_dec(v_x_842_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_847_, lean_object* v_msgData_848_, uint8_t v_severity_849_, uint8_t v_isSilent_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___y_857_; uint8_t v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; uint8_t v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; uint8_t v___y_898_; uint8_t v___y_899_; uint8_t v___y_900_; lean_object* v___y_901_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; uint8_t v___y_922_; lean_object* v___y_923_; uint8_t v___y_924_; uint8_t v___y_925_; lean_object* v___y_926_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; uint8_t v___y_934_; uint8_t v___y_935_; uint8_t v___y_936_; uint8_t v___x_941_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; uint8_t v___y_947_; uint8_t v___y_948_; uint8_t v___y_949_; uint8_t v___y_951_; uint8_t v___x_967_; 
v___x_941_ = 2;
v___x_967_ = l_Lean_instBEqMessageSeverity_beq(v_severity_849_, v___x_941_);
if (v___x_967_ == 0)
{
v___y_951_ = v___x_967_;
goto v___jp_950_;
}
else
{
uint8_t v___x_968_; 
lean_inc_ref(v_msgData_848_);
v___x_968_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_848_);
v___y_951_ = v___x_968_;
goto v___jp_950_;
}
v___jp_856_:
{
lean_object* v___x_866_; lean_object* v_toCold_867_; lean_object* v_currNamespace_868_; lean_object* v_openDecls_869_; lean_object* v_env_870_; lean_object* v_nextMacroScope_871_; lean_object* v_ngen_872_; lean_object* v_auxDeclNGen_873_; lean_object* v_traceState_874_; lean_object* v_cache_875_; lean_object* v_messages_876_; lean_object* v_infoState_877_; lean_object* v_snapshotTasks_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_892_; 
v___x_866_ = lean_st_ref_take(v___y_865_);
v_toCold_867_ = lean_ctor_get(v___y_864_, 0);
v_currNamespace_868_ = lean_ctor_get(v_toCold_867_, 4);
v_openDecls_869_ = lean_ctor_get(v_toCold_867_, 5);
v_env_870_ = lean_ctor_get(v___x_866_, 0);
v_nextMacroScope_871_ = lean_ctor_get(v___x_866_, 1);
v_ngen_872_ = lean_ctor_get(v___x_866_, 2);
v_auxDeclNGen_873_ = lean_ctor_get(v___x_866_, 3);
v_traceState_874_ = lean_ctor_get(v___x_866_, 4);
v_cache_875_ = lean_ctor_get(v___x_866_, 5);
v_messages_876_ = lean_ctor_get(v___x_866_, 6);
v_infoState_877_ = lean_ctor_get(v___x_866_, 7);
v_snapshotTasks_878_ = lean_ctor_get(v___x_866_, 8);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_892_ == 0)
{
v___x_880_ = v___x_866_;
v_isShared_881_ = v_isSharedCheck_892_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_snapshotTasks_878_);
lean_inc(v_infoState_877_);
lean_inc(v_messages_876_);
lean_inc(v_cache_875_);
lean_inc(v_traceState_874_);
lean_inc(v_auxDeclNGen_873_);
lean_inc(v_ngen_872_);
lean_inc(v_nextMacroScope_871_);
lean_inc(v_env_870_);
lean_dec(v___x_866_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_892_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
lean_inc(v_openDecls_869_);
lean_inc(v_currNamespace_868_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_currNamespace_868_);
lean_ctor_set(v___x_882_, 1, v_openDecls_869_);
v___x_883_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___y_860_);
lean_inc_ref(v___y_859_);
lean_inc_ref(v___y_857_);
v___x_884_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_884_, 0, v___y_857_);
lean_ctor_set(v___x_884_, 1, v___y_862_);
lean_ctor_set(v___x_884_, 2, v___y_863_);
lean_ctor_set(v___x_884_, 3, v___y_859_);
lean_ctor_set(v___x_884_, 4, v___x_883_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*5, v___y_858_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*5 + 1, v___y_861_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*5 + 2, v_isSilent_850_);
v___x_885_ = l_Lean_MessageLog_add(v___x_884_, v_messages_876_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 6, v___x_885_);
v___x_887_ = v___x_880_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_env_870_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_nextMacroScope_871_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_ngen_872_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v_auxDeclNGen_873_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v_traceState_874_);
lean_ctor_set(v_reuseFailAlloc_891_, 5, v_cache_875_);
lean_ctor_set(v_reuseFailAlloc_891_, 6, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_891_, 7, v_infoState_877_);
lean_ctor_set(v_reuseFailAlloc_891_, 8, v_snapshotTasks_878_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_st_ref_put(v___y_865_, v___x_887_);
v___x_889_ = lean_box(0);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
}
v___jp_893_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_917_; 
v___x_902_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_848_);
v___x_903_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_902_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_917_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_917_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_917_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_inc_ref_n(v___y_896_, 2);
v___x_908_ = l_Lean_FileMap_toPosition(v___y_896_, v___y_895_);
lean_dec(v___y_895_);
v___x_909_ = l_Lean_FileMap_toPosition(v___y_896_, v___y_901_);
lean_dec(v___y_901_);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
v___x_911_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_899_ == 0)
{
lean_del_object(v___x_906_);
lean_dec_ref(v___y_894_);
v___y_857_ = v___y_897_;
v___y_858_ = v___y_898_;
v___y_859_ = v___x_911_;
v___y_860_ = v_a_904_;
v___y_861_ = v___y_900_;
v___y_862_ = v___x_908_;
v___y_863_ = v___x_910_;
v___y_864_ = v___y_853_;
v___y_865_ = v___y_854_;
goto v___jp_856_;
}
else
{
uint8_t v___x_912_; 
lean_inc(v_a_904_);
v___x_912_ = l_Lean_MessageData_hasTag(v___y_894_, v_a_904_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_dec_ref_known(v___x_910_, 1);
lean_dec_ref(v___x_908_);
lean_dec(v_a_904_);
v___x_913_ = lean_box(0);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_913_);
v___x_915_ = v___x_906_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
lean_del_object(v___x_906_);
v___y_857_ = v___y_897_;
v___y_858_ = v___y_898_;
v___y_859_ = v___x_911_;
v___y_860_ = v_a_904_;
v___y_861_ = v___y_900_;
v___y_862_ = v___x_908_;
v___y_863_ = v___x_910_;
v___y_864_ = v___y_853_;
v___y_865_ = v___y_854_;
goto v___jp_856_;
}
}
}
}
v___jp_918_:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_Syntax_getTailPos_x3f(v___y_923_, v___y_922_);
lean_dec(v___y_923_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_inc(v___y_926_);
v___y_894_ = v___y_919_;
v___y_895_ = v___y_926_;
v___y_896_ = v___y_920_;
v___y_897_ = v___y_921_;
v___y_898_ = v___y_922_;
v___y_899_ = v___y_924_;
v___y_900_ = v___y_925_;
v___y_901_ = v___y_926_;
goto v___jp_893_;
}
else
{
lean_object* v_val_928_; 
v_val_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_val_928_);
lean_dec_ref_known(v___x_927_, 1);
v___y_894_ = v___y_919_;
v___y_895_ = v___y_926_;
v___y_896_ = v___y_920_;
v___y_897_ = v___y_921_;
v___y_898_ = v___y_922_;
v___y_899_ = v___y_924_;
v___y_900_ = v___y_925_;
v___y_901_ = v_val_928_;
goto v___jp_893_;
}
}
v___jp_929_:
{
lean_object* v_ref_937_; lean_object* v___x_938_; 
v_ref_937_ = l_Lean_replaceRef(v_ref_847_, v___y_932_);
v___x_938_ = l_Lean_Syntax_getPos_x3f(v_ref_937_, v___y_934_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v___y_919_ = v___y_930_;
v___y_920_ = v___y_931_;
v___y_921_ = v___y_933_;
v___y_922_ = v___y_934_;
v___y_923_ = v_ref_937_;
v___y_924_ = v___y_935_;
v___y_925_ = v___y_936_;
v___y_926_ = v___x_939_;
goto v___jp_918_;
}
else
{
lean_object* v_val_940_; 
v_val_940_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v___x_938_, 1);
v___y_919_ = v___y_930_;
v___y_920_ = v___y_931_;
v___y_921_ = v___y_933_;
v___y_922_ = v___y_934_;
v___y_923_ = v_ref_937_;
v___y_924_ = v___y_935_;
v___y_925_ = v___y_936_;
v___y_926_ = v_val_940_;
goto v___jp_918_;
}
}
v___jp_942_:
{
if (v___y_949_ == 0)
{
v___y_930_ = v___y_943_;
v___y_931_ = v___y_944_;
v___y_932_ = v___y_946_;
v___y_933_ = v___y_945_;
v___y_934_ = v___y_947_;
v___y_935_ = v___y_948_;
v___y_936_ = v_severity_849_;
goto v___jp_929_;
}
else
{
v___y_930_ = v___y_943_;
v___y_931_ = v___y_944_;
v___y_932_ = v___y_946_;
v___y_933_ = v___y_945_;
v___y_934_ = v___y_947_;
v___y_935_ = v___y_948_;
v___y_936_ = v___x_941_;
goto v___jp_929_;
}
}
v___jp_950_:
{
if (v___y_951_ == 0)
{
lean_object* v_toCold_952_; lean_object* v_ref_953_; uint8_t v_suppressElabErrors_954_; lean_object* v_fileName_955_; lean_object* v_fileMap_956_; lean_object* v_options_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___f_960_; uint8_t v___x_961_; uint8_t v___x_962_; 
v_toCold_952_ = lean_ctor_get(v___y_853_, 0);
v_ref_953_ = lean_ctor_get(v___y_853_, 2);
v_suppressElabErrors_954_ = lean_ctor_get_uint8(v___y_853_, sizeof(void*)*3 + 1);
v_fileName_955_ = lean_ctor_get(v_toCold_952_, 0);
v_fileMap_956_ = lean_ctor_get(v_toCold_952_, 1);
v_options_957_ = lean_ctor_get(v_toCold_952_, 2);
v___x_958_ = lean_box(v_suppressElabErrors_954_);
v___x_959_ = lean_box(v___y_951_);
v___f_960_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_960_, 0, v___x_958_);
lean_closure_set(v___f_960_, 1, v___x_959_);
v___x_961_ = 1;
v___x_962_ = l_Lean_instBEqMessageSeverity_beq(v_severity_849_, v___x_961_);
if (v___x_962_ == 0)
{
v___y_943_ = v___f_960_;
v___y_944_ = v_fileMap_956_;
v___y_945_ = v_fileName_955_;
v___y_946_ = v_ref_953_;
v___y_947_ = v___y_951_;
v___y_948_ = v_suppressElabErrors_954_;
v___y_949_ = v___x_962_;
goto v___jp_942_;
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = l_Lean_warningAsError;
v___x_964_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_957_, v___x_963_);
v___y_943_ = v___f_960_;
v___y_944_ = v_fileMap_956_;
v___y_945_ = v_fileName_955_;
v___y_946_ = v_ref_953_;
v___y_947_ = v___y_951_;
v___y_948_ = v_suppressElabErrors_954_;
v___y_949_ = v___x_964_;
goto v___jp_942_;
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v_msgData_848_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_969_, lean_object* v_msgData_970_, lean_object* v_severity_971_, lean_object* v_isSilent_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v_severity_boxed_978_; uint8_t v_isSilent_boxed_979_; lean_object* v_res_980_; 
v_severity_boxed_978_ = lean_unbox(v_severity_971_);
v_isSilent_boxed_979_ = lean_unbox(v_isSilent_972_);
v_res_980_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_969_, v_msgData_970_, v_severity_boxed_978_, v_isSilent_boxed_979_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v_ref_969_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_981_, size_t v_sz_982_, size_t v_i_983_, lean_object* v_b_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = lean_usize_dec_lt(v_i_983_, v_sz_982_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_b_984_);
return v___x_993_;
}
else
{
lean_object* v_ref_994_; lean_object* v_a_995_; uint8_t v_severity_996_; uint8_t v_isSilent_997_; lean_object* v_data_998_; lean_object* v___x_999_; 
v_ref_994_ = lean_ctor_get(v___y_989_, 2);
v_a_995_ = lean_array_uget_borrowed(v_as_981_, v_i_983_);
v_severity_996_ = lean_ctor_get_uint8(v_a_995_, sizeof(void*)*5 + 1);
v_isSilent_997_ = lean_ctor_get_uint8(v_a_995_, sizeof(void*)*5 + 2);
v_data_998_ = lean_ctor_get(v_a_995_, 4);
lean_inc(v_data_998_);
v___x_999_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_994_, v_data_998_, v_severity_996_, v_isSilent_997_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; 
lean_dec_ref_known(v___x_999_, 1);
v___x_1000_ = lean_box(0);
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_add(v_i_983_, v___x_1001_);
v_i_983_ = v___x_1002_;
v_b_984_ = v___x_1000_;
goto _start;
}
else
{
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_1004_, lean_object* v_sz_1005_, lean_object* v_i_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
size_t v_sz_boxed_1015_; size_t v_i_boxed_1016_; lean_object* v_res_1017_; 
v_sz_boxed_1015_ = lean_unbox_usize(v_sz_1005_);
lean_dec(v_sz_1005_);
v_i_boxed_1016_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_1004_, v_sz_boxed_1015_, v_i_boxed_1016_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v_as_1004_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v_infoState_1022_; lean_object* v_env_1023_; lean_object* v_nextMacroScope_1024_; lean_object* v_ngen_1025_; lean_object* v_auxDeclNGen_1026_; lean_object* v_traceState_1027_; lean_object* v_cache_1028_; lean_object* v_messages_1029_; lean_object* v_snapshotTasks_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1050_; 
v___x_1021_ = lean_st_ref_take(v___y_1019_);
v_infoState_1022_ = lean_ctor_get(v___x_1021_, 7);
v_env_1023_ = lean_ctor_get(v___x_1021_, 0);
v_nextMacroScope_1024_ = lean_ctor_get(v___x_1021_, 1);
v_ngen_1025_ = lean_ctor_get(v___x_1021_, 2);
v_auxDeclNGen_1026_ = lean_ctor_get(v___x_1021_, 3);
v_traceState_1027_ = lean_ctor_get(v___x_1021_, 4);
v_cache_1028_ = lean_ctor_get(v___x_1021_, 5);
v_messages_1029_ = lean_ctor_get(v___x_1021_, 6);
v_snapshotTasks_1030_ = lean_ctor_get(v___x_1021_, 8);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1032_ = v___x_1021_;
v_isShared_1033_ = v_isSharedCheck_1050_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_snapshotTasks_1030_);
lean_inc(v_infoState_1022_);
lean_inc(v_messages_1029_);
lean_inc(v_cache_1028_);
lean_inc(v_traceState_1027_);
lean_inc(v_auxDeclNGen_1026_);
lean_inc(v_ngen_1025_);
lean_inc(v_nextMacroScope_1024_);
lean_inc(v_env_1023_);
lean_dec(v___x_1021_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1050_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_assignment_1034_; lean_object* v_lazyAssignment_1035_; lean_object* v_trees_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1049_; 
v_assignment_1034_ = lean_ctor_get(v_infoState_1022_, 0);
v_lazyAssignment_1035_ = lean_ctor_get(v_infoState_1022_, 1);
v_trees_1036_ = lean_ctor_get(v_infoState_1022_, 2);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_infoState_1022_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1038_ = v_infoState_1022_;
v_isShared_1039_ = v_isSharedCheck_1049_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_trees_1036_);
lean_inc(v_lazyAssignment_1035_);
lean_inc(v_assignment_1034_);
lean_dec(v_infoState_1022_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1049_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_assignment_1034_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_lazyAssignment_1035_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_trees_1036_);
v___x_1041_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*3, v_flag_1018_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 7, v___x_1041_);
v___x_1043_ = v___x_1032_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_env_1023_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_nextMacroScope_1024_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_ngen_1025_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_auxDeclNGen_1026_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_traceState_1027_);
lean_ctor_set(v_reuseFailAlloc_1047_, 5, v_cache_1028_);
lean_ctor_set(v_reuseFailAlloc_1047_, 6, v_messages_1029_);
lean_ctor_set(v_reuseFailAlloc_1047_, 7, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1047_, 8, v_snapshotTasks_1030_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = lean_st_ref_put(v___y_1019_, v___x_1043_);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v_flag_boxed_1054_; lean_object* v_res_1055_; 
v_flag_boxed_1054_ = lean_unbox(v_flag_1051_);
v_res_1055_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1054_, v___y_1052_);
lean_dec(v___y_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v_infoState_1066_; uint8_t v_enabled_1067_; lean_object* v_a_1069_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1065_ = lean_st_ref_get(v___y_1063_);
v_infoState_1066_ = lean_ctor_get(v___x_1065_, 7);
lean_inc_ref(v_infoState_1066_);
lean_dec(v___x_1065_);
v_enabled_1067_ = lean_ctor_get_uint8(v_infoState_1066_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1066_);
v___x_1079_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1056_, v___y_1063_);
lean_dec_ref(v___x_1079_);
lean_inc(v___y_1063_);
lean_inc_ref(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
v___x_1080_ = lean_apply_7(v_x_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, lean_box(0));
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1067_, v___y_1063_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___x_1082_, 0);
lean_dec(v_unused_1090_);
v___x_1084_ = v___x_1082_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_dec(v___x_1082_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v_a_1081_);
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1081_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v_a_1091_; 
v_a_1091_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1080_, 1);
v_a_1069_ = v_a_1091_;
goto v___jp_1068_;
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v___x_1070_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1067_, v___y_1063_);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v___x_1070_, 0);
lean_dec(v_unused_1078_);
v___x_1072_ = v___x_1070_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_dec(v___x_1070_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 0, v_a_1069_);
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1069_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
uint8_t v_flag_boxed_1101_; lean_object* v_res_1102_; 
v_flag_boxed_1101_ = lean_unbox(v_flag_1092_);
v_res_1102_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1101_, v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1103_, lean_object* v_binders_1104_, lean_object* v_blocks_1105_, lean_object* v_fileMap_x3f_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1112_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v_a_1117_; size_t v_sz_1135_; size_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___y_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v_sz_1135_ = lean_array_size(v_blocks_1105_);
v___x_1136_ = ((size_t)0ULL);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1135_, v___x_1136_, v_blocks_1105_);
v___x_1138_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1138_, 0, v___x_1137_);
v___x_1139_ = 1;
v___x_1140_ = lean_box(v___x_1139_);
v___y_1141_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1141_, 0, v_fileMap_x3f_1106_);
lean_closure_set(v___y_1141_, 1, v_declName_1103_);
lean_closure_set(v___y_1141_, 2, v_binders_1104_);
lean_closure_set(v___y_1141_, 3, v___x_1138_);
lean_closure_set(v___y_1141_, 4, v___x_1140_);
v___x_1142_ = 0;
v___x_1143_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1142_, v___y_1141_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1112_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = l_Lean_Core_setMessageLog___redArg(v_a_1115_, v_a_1112_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; size_t v_sz_1150_; lean_object* v___x_1151_; 
lean_dec_ref_known(v___x_1147_, 1);
v___x_1148_ = l_Lean_MessageLog_toArray(v_a_1146_);
lean_dec(v_a_1146_);
v___x_1149_ = lean_box(0);
v_sz_1150_ = lean_array_size(v___x_1148_);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1148_, v_sz_1150_, v___x_1136_, v___x_1149_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec_ref(v___x_1148_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1176_; 
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v___x_1151_, 0);
lean_dec(v_unused_1177_);
v___x_1153_ = v___x_1151_;
v_isShared_1154_ = v_isSharedCheck_1176_;
goto v_resetjp_1152_;
}
else
{
lean_dec(v___x_1151_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1176_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_fst_1155_; lean_object* v_snd_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1175_; 
v_fst_1155_ = lean_ctor_get(v_a_1144_, 0);
v_snd_1156_ = lean_ctor_get(v_a_1144_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1158_ = v_a_1144_;
v_isShared_1159_ = v_isSharedCheck_1175_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snd_1156_);
lean_inc(v_fst_1155_);
lean_dec(v_a_1144_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1175_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_fst_1160_; lean_object* v_snd_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1174_; 
v_fst_1160_ = lean_ctor_get(v_fst_1155_, 0);
v_snd_1161_ = lean_ctor_get(v_fst_1155_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_fst_1155_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1163_ = v_fst_1155_;
v_isShared_1164_ = v_isSharedCheck_1174_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_snd_1161_);
lean_inc(v_fst_1160_);
lean_dec(v_fst_1155_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1174_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_fst_1160_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_snd_1161_);
v___x_1166_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1166_);
v___x_1168_ = v___x_1158_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_snd_1156_);
v___x_1168_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1168_);
v___x_1170_ = v___x_1153_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_a_1144_);
v_a_1178_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1151_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1151_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_a_1146_);
lean_dec(v_a_1144_);
v_a_1186_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1147_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1147_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; 
lean_dec(v_a_1144_);
v_a_1194_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1145_, 1);
v_a_1117_ = v_a_1194_;
goto v___jp_1116_;
}
}
else
{
lean_object* v_a_1195_; 
v_a_1195_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1143_, 1);
v_a_1117_ = v_a_1195_;
goto v___jp_1116_;
}
v___jp_1116_:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Core_setMessageLog___redArg(v_a_1115_, v_a_1112_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1126_);
v___x_1120_ = v___x_1118_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v___x_1118_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
lean_ctor_set(v___x_1120_, 0, v_a_1117_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1117_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v_a_1117_);
v_a_1127_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1118_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1118_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_fileMap_x3f_1106_);
lean_dec_ref(v_blocks_1105_);
lean_dec(v_binders_1104_);
lean_dec(v_declName_1103_);
v_a_1196_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1114_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1114_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1204_, lean_object* v_binders_1205_, lean_object* v_blocks_1206_, lean_object* v_fileMap_x3f_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1204_, v_binders_1205_, v_blocks_1206_, v_fileMap_x3f_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1216_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v_flag_boxed_1233_; lean_object* v_res_1234_; 
v_flag_boxed_1233_ = lean_unbox(v_flag_1225_);
v_res_1234_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1233_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1235_, uint8_t v_flag_1236_, lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1236_, v_x_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_flag_1247_, lean_object* v_x_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v_flag_boxed_1256_; lean_object* v_res_1257_; 
v_flag_boxed_1256_ = lean_unbox(v_flag_1247_);
v_res_1257_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1246_, v_flag_boxed_1256_, v_x_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1258_, lean_object* v_msgData_1259_, uint8_t v_severity_1260_, uint8_t v_isSilent_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1258_, v_msgData_1259_, v_severity_1260_, v_isSilent_1261_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1270_, lean_object* v_msgData_1271_, lean_object* v_severity_1272_, lean_object* v_isSilent_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v_severity_boxed_1281_; uint8_t v_isSilent_boxed_1282_; lean_object* v_res_1283_; 
v_severity_boxed_1281_ = lean_unbox(v_severity_1272_);
v_isSilent_boxed_1282_ = lean_unbox(v_isSilent_1273_);
v_res_1283_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1270_, v_msgData_1271_, v_severity_boxed_1281_, v_isSilent_boxed_1282_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v_ref_1270_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1284_, uint8_t v_severity_1285_, uint8_t v_isSilent_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_ref_1292_; lean_object* v___x_1293_; 
v_ref_1292_ = lean_ctor_get(v___y_1289_, 2);
v___x_1293_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1292_, v_msgData_1284_, v_severity_1285_, v_isSilent_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1294_, lean_object* v_severity_1295_, lean_object* v_isSilent_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v_severity_boxed_1302_; uint8_t v_isSilent_boxed_1303_; lean_object* v_res_1304_; 
v_severity_boxed_1302_ = lean_unbox(v_severity_1295_);
v_isSilent_boxed_1303_ = lean_unbox(v_isSilent_1296_);
v_res_1304_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1294_, v_severity_boxed_1302_, v_isSilent_boxed_1303_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = 2;
v___x_1314_ = 0;
v___x_1315_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1305_, v___x_1313_, v___x_1314_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1325_, size_t v_sz_1326_, size_t v_i_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_usize_dec_lt(v_i_1327_, v_sz_1326_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_b_1328_);
return v___x_1337_;
}
else
{
lean_object* v_a_1338_; lean_object* v_snd_1339_; lean_object* v_snd_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_a_1338_ = lean_array_uget_borrowed(v_as_1325_, v_i_1327_);
v_snd_1339_ = lean_ctor_get(v_a_1338_, 1);
v_snd_1340_ = lean_ctor_get(v_snd_1339_, 1);
lean_inc(v_snd_1340_);
v___x_1341_ = l_Lean_Parser_Error_toString(v_snd_1340_);
v___x_1342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
v___x_1343_ = l_Lean_MessageData_ofFormat(v___x_1342_);
v___x_1344_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1343_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; 
lean_dec_ref_known(v___x_1344_, 1);
v___x_1345_ = lean_box(0);
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1327_, v___x_1346_);
v_i_1327_ = v___x_1347_;
v_b_1328_ = v___x_1345_;
goto _start;
}
else
{
return v___x_1344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1349_, lean_object* v_sz_1350_, lean_object* v_i_1351_, lean_object* v_b_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
size_t v_sz_boxed_1360_; size_t v_i_boxed_1361_; lean_object* v_res_1362_; 
v_sz_boxed_1360_ = lean_unbox_usize(v_sz_1350_);
lean_dec(v_sz_1350_);
v_i_boxed_1361_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1349_, v_sz_boxed_1360_, v_i_boxed_1361_, v_b_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v_as_1349_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1382_, lean_object* v_binders_1383_, lean_object* v_docComment_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1392_; lean_object* v_toCold_1393_; lean_object* v_env_1394_; lean_object* v_fileName_1395_; lean_object* v_options_1396_; lean_object* v_currNamespace_1397_; lean_object* v_openDecls_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1392_ = lean_st_ref_get(v_a_1390_);
v_toCold_1393_ = lean_ctor_get(v_a_1389_, 0);
v_env_1394_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref_n(v_env_1394_, 2);
lean_dec(v___x_1392_);
v_fileName_1395_ = lean_ctor_get(v_toCold_1393_, 0);
v_options_1396_ = lean_ctor_get(v_toCold_1393_, 2);
v_currNamespace_1397_ = lean_ctor_get(v_toCold_1393_, 4);
v_openDecls_1398_ = lean_ctor_get(v_toCold_1393_, 5);
v___x_1399_ = lean_string_utf8_byte_size(v_docComment_1384_);
lean_inc_ref_n(v_docComment_1384_, 2);
v___x_1400_ = l_Lean_FileMap_ofString(v_docComment_1384_);
lean_inc_ref(v___x_1400_);
lean_inc_ref(v_fileName_1395_);
v___x_1401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1401_, 0, v_docComment_1384_);
lean_ctor_set(v___x_1401_, 1, v_fileName_1395_);
lean_ctor_set(v___x_1401_, 2, v___x_1400_);
lean_ctor_set(v___x_1401_, 3, v___x_1399_);
lean_inc(v_openDecls_1398_);
lean_inc(v_currNamespace_1397_);
lean_inc_ref(v_options_1396_);
v___x_1402_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1402_, 0, v_env_1394_);
lean_ctor_set(v___x_1402_, 1, v_options_1396_);
lean_ctor_set(v___x_1402_, 2, v_currNamespace_1397_);
lean_ctor_set(v___x_1402_, 3, v_openDecls_1398_);
v___x_1403_ = l_Lean_Parser_mkParserState(v_docComment_1384_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__1));
v___x_1406_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1407_ = l_Lean_Parser_getTokenTable(v_env_1394_);
lean_inc_ref(v___x_1407_);
lean_inc_ref(v___x_1402_);
lean_inc_ref_n(v___x_1401_, 2);
v___x_1408_ = l_Lean_Parser_ParserFn_run(v___x_1406_, v___x_1401_, v___x_1402_, v___x_1407_, v___x_1403_);
lean_inc_ref(v___x_1408_);
v___x_1409_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v___x_1401_, v___x_1402_, v___x_1407_, v_docComment_1384_, v___x_1405_, v___x_1408_);
v___x_1410_ = lean_array_get_size(v___x_1409_);
v___x_1411_ = lean_nat_dec_eq(v___x_1410_, v___x_1404_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; size_t v_sz_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
lean_dec_ref(v___x_1408_);
lean_dec_ref_known(v___x_1401_, 4);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_docComment_1384_);
lean_dec(v_binders_1383_);
lean_dec(v_declName_1382_);
v___x_1412_ = lean_box(0);
v_sz_1413_ = lean_array_size(v___x_1409_);
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1409_, v_sz_1413_, v___x_1414_, v___x_1412_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
lean_dec_ref(v___x_1409_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1424_);
v___x_1417_ = v___x_1415_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v___x_1415_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1425_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1415_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_stxStack_1433_; lean_object* v_pos_1434_; uint8_t v___x_1435_; 
lean_dec_ref(v___x_1409_);
v_stxStack_1433_ = lean_ctor_get(v___x_1408_, 0);
lean_inc_ref(v_stxStack_1433_);
v_pos_1434_ = lean_ctor_get(v___x_1408_, 2);
lean_inc(v_pos_1434_);
lean_dec_ref(v___x_1408_);
v___x_1435_ = l_Lean_Parser_InputContext_atEnd(v___x_1401_, v_pos_1434_);
lean_dec_ref_known(v___x_1401_, 4);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; uint32_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec_ref(v_stxStack_1433_);
lean_dec_ref(v___x_1400_);
lean_dec(v_binders_1383_);
lean_dec(v_declName_1382_);
v___x_1436_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__0));
v___x_1437_ = lean_string_utf8_get(v_docComment_1384_, v_pos_1434_);
lean_dec(v_pos_1434_);
lean_dec_ref(v_docComment_1384_);
v___x_1438_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_1439_ = lean_string_push(v___x_1438_, v___x_1437_);
v___x_1440_ = lean_string_append(v___x_1436_, v___x_1439_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__1));
v___x_1442_ = lean_string_append(v___x_1440_, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
v___x_1444_ = l_Lean_MessageData_ofFormat(v___x_1443_);
v___x_1445_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1444_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1454_);
v___x_1447_ = v___x_1445_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v___x_1445_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_a_1455_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1445_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1445_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v_pos_1434_);
lean_dec_ref(v_docComment_1384_);
v___x_1463_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1433_);
lean_dec_ref(v_stxStack_1433_);
v___x_1464_ = l_Lean_TSyntax_getVersoBlocks(v___x_1463_);
lean_dec(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1400_);
v___x_1466_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1382_, v_binders_1383_, v___x_1464_, v___x_1465_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1467_, lean_object* v_binders_1468_, lean_object* v_docComment_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_versoDocStringOfText(v_declName_1467_, v_binders_1468_, v_docComment_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1478_, uint8_t v_severity_1479_, uint8_t v_isSilent_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1478_, v_severity_1479_, v_isSilent_1480_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1489_, lean_object* v_severity_1490_, lean_object* v_isSilent_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v_severity_boxed_1499_; uint8_t v_isSilent_boxed_1500_; lean_object* v_res_1501_; 
v_severity_boxed_1499_ = lean_unbox(v_severity_1490_);
v_isSilent_boxed_1500_ = lean_unbox(v_isSilent_1491_);
v_res_1501_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1489_, v_severity_boxed_1499_, v_isSilent_boxed_1500_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1501_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v_suppressElabErrors_1502_, uint8_t v___x_1503_, lean_object* v_x_1504_){
_start:
{
if (lean_obj_tag(v_x_1504_) == 1)
{
lean_object* v_pre_1505_; 
v_pre_1505_ = lean_ctor_get(v_x_1504_, 0);
switch(lean_obj_tag(v_pre_1505_))
{
case 1:
{
lean_object* v_pre_1506_; 
v_pre_1506_ = lean_ctor_get(v_pre_1505_, 0);
switch(lean_obj_tag(v_pre_1506_))
{
case 0:
{
lean_object* v_str_1507_; lean_object* v_str_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_str_1507_ = lean_ctor_get(v_x_1504_, 1);
v_str_1508_ = lean_ctor_get(v_pre_1505_, 1);
v___x_1509_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1510_ = lean_string_dec_eq(v_str_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1512_ = lean_string_dec_eq(v_str_1508_, v___x_1511_);
if (v___x_1512_ == 0)
{
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1514_ = lean_string_dec_eq(v_str_1507_, v___x_1513_);
if (v___x_1514_ == 0)
{
return v___x_1514_;
}
else
{
return v_suppressElabErrors_1502_;
}
}
}
else
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1516_ = lean_string_dec_eq(v_str_1507_, v___x_1515_);
if (v___x_1516_ == 0)
{
return v___x_1516_;
}
else
{
return v_suppressElabErrors_1502_;
}
}
}
case 1:
{
lean_object* v_pre_1517_; 
v_pre_1517_ = lean_ctor_get(v_pre_1506_, 0);
if (lean_obj_tag(v_pre_1517_) == 0)
{
lean_object* v_str_1518_; lean_object* v_str_1519_; lean_object* v_str_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v_str_1518_ = lean_ctor_get(v_x_1504_, 1);
v_str_1519_ = lean_ctor_get(v_pre_1505_, 1);
v_str_1520_ = lean_ctor_get(v_pre_1506_, 1);
v___x_1521_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1522_ = lean_string_dec_eq(v_str_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1524_ = lean_string_dec_eq(v_str_1519_, v___x_1523_);
if (v___x_1524_ == 0)
{
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1526_ = lean_string_dec_eq(v_str_1518_, v___x_1525_);
if (v___x_1526_ == 0)
{
return v___x_1526_;
}
else
{
return v_suppressElabErrors_1502_;
}
}
}
}
else
{
return v___x_1503_;
}
}
default: 
{
return v___x_1503_;
}
}
}
case 0:
{
lean_object* v_str_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v_str_1527_ = lean_ctor_get(v_x_1504_, 1);
v___x_1528_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1529_ = lean_string_dec_eq(v_str_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
return v___x_1529_;
}
else
{
return v_suppressElabErrors_1502_;
}
}
default: 
{
return v___x_1503_;
}
}
}
else
{
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1530_, lean_object* v___x_1531_, lean_object* v_x_1532_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1533_; uint8_t v___x_10495__boxed_1534_; uint8_t v_res_1535_; lean_object* v_r_1536_; 
v_suppressElabErrors_boxed_1533_ = lean_unbox(v_suppressElabErrors_1530_);
v___x_10495__boxed_1534_ = lean_unbox(v___x_1531_);
v_res_1535_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v_suppressElabErrors_boxed_1533_, v___x_10495__boxed_1534_, v_x_1532_);
lean_dec(v_x_1532_);
v_r_1536_ = lean_box(v_res_1535_);
return v_r_1536_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v_suppressElabErrors_1537_, uint8_t v___x_1538_, lean_object* v_x_1539_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 1)
{
lean_object* v_pre_1540_; 
v_pre_1540_ = lean_ctor_get(v_x_1539_, 0);
switch(lean_obj_tag(v_pre_1540_))
{
case 1:
{
lean_object* v_pre_1541_; 
v_pre_1541_ = lean_ctor_get(v_pre_1540_, 0);
switch(lean_obj_tag(v_pre_1541_))
{
case 0:
{
lean_object* v_str_1542_; lean_object* v_str_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v_str_1542_ = lean_ctor_get(v_x_1539_, 1);
v_str_1543_ = lean_ctor_get(v_pre_1540_, 1);
v___x_1544_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1545_ = lean_string_dec_eq(v_str_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1547_ = lean_string_dec_eq(v_str_1543_, v___x_1546_);
if (v___x_1547_ == 0)
{
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1549_ = lean_string_dec_eq(v_str_1542_, v___x_1548_);
if (v___x_1549_ == 0)
{
return v___x_1549_;
}
else
{
return v_suppressElabErrors_1537_;
}
}
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1551_ = lean_string_dec_eq(v_str_1542_, v___x_1550_);
if (v___x_1551_ == 0)
{
return v___x_1551_;
}
else
{
return v_suppressElabErrors_1537_;
}
}
}
case 1:
{
lean_object* v_pre_1552_; 
v_pre_1552_ = lean_ctor_get(v_pre_1541_, 0);
if (lean_obj_tag(v_pre_1552_) == 0)
{
lean_object* v_str_1553_; lean_object* v_str_1554_; lean_object* v_str_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_str_1553_ = lean_ctor_get(v_x_1539_, 1);
v_str_1554_ = lean_ctor_get(v_pre_1540_, 1);
v_str_1555_ = lean_ctor_get(v_pre_1541_, 1);
v___x_1556_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1557_ = lean_string_dec_eq(v_str_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1559_ = lean_string_dec_eq(v_str_1554_, v___x_1558_);
if (v___x_1559_ == 0)
{
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1561_ = lean_string_dec_eq(v_str_1553_, v___x_1560_);
if (v___x_1561_ == 0)
{
return v___x_1561_;
}
else
{
return v_suppressElabErrors_1537_;
}
}
}
}
else
{
return v___x_1538_;
}
}
default: 
{
return v___x_1538_;
}
}
}
case 0:
{
lean_object* v_str_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_str_1562_ = lean_ctor_get(v_x_1539_, 1);
v___x_1563_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1564_ = lean_string_dec_eq(v_str_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
return v___x_1564_;
}
else
{
return v_suppressElabErrors_1537_;
}
}
default: 
{
return v___x_1538_;
}
}
}
else
{
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1565_, lean_object* v___x_1566_, lean_object* v_x_1567_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1568_; uint8_t v___x_10559__boxed_1569_; uint8_t v_res_1570_; lean_object* v_r_1571_; 
v_suppressElabErrors_boxed_1568_ = lean_unbox(v_suppressElabErrors_1565_);
v___x_10559__boxed_1569_ = lean_unbox(v___x_1566_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v_suppressElabErrors_boxed_1568_, v___x_10559__boxed_1569_, v_x_1567_);
lean_dec(v_x_1567_);
v_r_1571_ = lean_box(v_res_1570_);
return v_r_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v_ictx_1572_, lean_object* v___x_1573_, lean_object* v_as_1574_, size_t v_sz_1575_, size_t v_i_1576_, lean_object* v_b_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_a_1582_; uint8_t v___x_1586_; 
v___x_1586_ = lean_usize_dec_lt(v_i_1576_, v_sz_1575_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref(v_ictx_1572_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_b_1577_);
return v___x_1587_;
}
else
{
lean_object* v_a_1588_; lean_object* v_snd_1589_; lean_object* v_fst_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1656_; 
v_a_1588_ = lean_array_uget(v_as_1574_, v_i_1576_);
v_snd_1589_ = lean_ctor_get(v_a_1588_, 1);
v_fst_1590_ = lean_ctor_get(v_a_1588_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_a_1588_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1592_ = v_a_1588_;
v_isShared_1593_ = v_isSharedCheck_1656_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_snd_1589_);
lean_inc(v_fst_1590_);
lean_dec(v_a_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1656_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_snd_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1654_; 
v_snd_1594_ = lean_ctor_get(v_snd_1589_, 1);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_snd_1589_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v_snd_1589_, 0);
lean_dec(v_unused_1655_);
v___x_1596_ = v_snd_1589_;
v_isShared_1597_ = v_isSharedCheck_1654_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_snd_1594_);
lean_dec(v_snd_1589_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1654_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
uint8_t v_suppressElabErrors_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___y_1602_; lean_object* v___y_1603_; 
v_suppressElabErrors_1598_ = lean_ctor_get_uint8(v___y_1578_, sizeof(void*)*3 + 1);
v___x_1599_ = lean_box(0);
lean_inc_ref(v_ictx_1572_);
v___x_1600_ = l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(v_ictx_1572_, v_fst_1590_, v_snd_1594_);
if (v_suppressElabErrors_1598_ == 0)
{
v___y_1602_ = v___y_1578_;
v___y_1603_ = v___y_1579_;
goto v___jp_1601_;
}
else
{
lean_object* v_data_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___f_1652_; uint8_t v___x_1653_; 
v_data_1647_ = lean_ctor_get(v___x_1600_, 4);
lean_inc(v_data_1647_);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_nat_dec_eq(v___x_1573_, v___x_1648_);
v___x_1650_ = lean_box(v_suppressElabErrors_1598_);
v___x_1651_ = lean_box(v___x_1649_);
v___f_1652_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1652_, 0, v___x_1650_);
lean_closure_set(v___f_1652_, 1, v___x_1651_);
v___x_1653_ = l_Lean_MessageData_hasTag(v___f_1652_, v_data_1647_);
if (v___x_1653_ == 0)
{
lean_dec_ref(v___x_1600_);
lean_del_object(v___x_1596_);
lean_del_object(v___x_1592_);
v_a_1582_ = v___x_1599_;
goto v___jp_1581_;
}
else
{
v___y_1602_ = v___y_1578_;
v___y_1603_ = v___y_1579_;
goto v___jp_1601_;
}
}
v___jp_1601_:
{
lean_object* v___x_1604_; lean_object* v_toCold_1605_; lean_object* v_fileName_1606_; lean_object* v_pos_1607_; lean_object* v_endPos_1608_; uint8_t v_keepFullRange_1609_; uint8_t v_severity_1610_; uint8_t v_isSilent_1611_; lean_object* v_caption_1612_; lean_object* v_data_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1646_; 
v___x_1604_ = lean_st_ref_take(v___y_1603_);
v_toCold_1605_ = lean_ctor_get(v___y_1602_, 0);
v_fileName_1606_ = lean_ctor_get(v___x_1600_, 0);
v_pos_1607_ = lean_ctor_get(v___x_1600_, 1);
v_endPos_1608_ = lean_ctor_get(v___x_1600_, 2);
v_keepFullRange_1609_ = lean_ctor_get_uint8(v___x_1600_, sizeof(void*)*5);
v_severity_1610_ = lean_ctor_get_uint8(v___x_1600_, sizeof(void*)*5 + 1);
v_isSilent_1611_ = lean_ctor_get_uint8(v___x_1600_, sizeof(void*)*5 + 2);
v_caption_1612_ = lean_ctor_get(v___x_1600_, 3);
v_data_1613_ = lean_ctor_get(v___x_1600_, 4);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1615_ = v___x_1600_;
v_isShared_1616_ = v_isSharedCheck_1646_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_data_1613_);
lean_inc(v_caption_1612_);
lean_inc(v_endPos_1608_);
lean_inc(v_pos_1607_);
lean_inc(v_fileName_1606_);
lean_dec(v___x_1600_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1646_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_currNamespace_1617_; lean_object* v_openDecls_1618_; lean_object* v_env_1619_; lean_object* v_nextMacroScope_1620_; lean_object* v_ngen_1621_; lean_object* v_auxDeclNGen_1622_; lean_object* v_traceState_1623_; lean_object* v_cache_1624_; lean_object* v_messages_1625_; lean_object* v_infoState_1626_; lean_object* v_snapshotTasks_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1645_; 
v_currNamespace_1617_ = lean_ctor_get(v_toCold_1605_, 4);
v_openDecls_1618_ = lean_ctor_get(v_toCold_1605_, 5);
v_env_1619_ = lean_ctor_get(v___x_1604_, 0);
v_nextMacroScope_1620_ = lean_ctor_get(v___x_1604_, 1);
v_ngen_1621_ = lean_ctor_get(v___x_1604_, 2);
v_auxDeclNGen_1622_ = lean_ctor_get(v___x_1604_, 3);
v_traceState_1623_ = lean_ctor_get(v___x_1604_, 4);
v_cache_1624_ = lean_ctor_get(v___x_1604_, 5);
v_messages_1625_ = lean_ctor_get(v___x_1604_, 6);
v_infoState_1626_ = lean_ctor_get(v___x_1604_, 7);
v_snapshotTasks_1627_ = lean_ctor_get(v___x_1604_, 8);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1629_ = v___x_1604_;
v_isShared_1630_ = v_isSharedCheck_1645_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_snapshotTasks_1627_);
lean_inc(v_infoState_1626_);
lean_inc(v_messages_1625_);
lean_inc(v_cache_1624_);
lean_inc(v_traceState_1623_);
lean_inc(v_auxDeclNGen_1622_);
lean_inc(v_ngen_1621_);
lean_inc(v_nextMacroScope_1620_);
lean_inc(v_env_1619_);
lean_dec(v___x_1604_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1645_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
lean_inc(v_openDecls_1618_);
lean_inc(v_currNamespace_1617_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v_openDecls_1618_);
lean_ctor_set(v___x_1596_, 0, v_currNamespace_1617_);
v___x_1632_ = v___x_1596_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_currNamespace_1617_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_openDecls_1618_);
v___x_1632_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1634_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 4);
lean_ctor_set(v___x_1592_, 1, v_data_1613_);
lean_ctor_set(v___x_1592_, 0, v___x_1632_);
v___x_1634_ = v___x_1592_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_data_1613_);
v___x_1634_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 4, v___x_1634_);
v___x_1636_ = v___x_1615_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_fileName_1606_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_pos_1607_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_endPos_1608_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v_caption_1612_);
lean_ctor_set(v_reuseFailAlloc_1642_, 4, v___x_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1642_, sizeof(void*)*5, v_keepFullRange_1609_);
lean_ctor_set_uint8(v_reuseFailAlloc_1642_, sizeof(void*)*5 + 1, v_severity_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1642_, sizeof(void*)*5 + 2, v_isSilent_1611_);
v___x_1636_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = l_Lean_MessageLog_add(v___x_1636_, v_messages_1625_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 6, v___x_1637_);
v___x_1639_ = v___x_1629_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_env_1619_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_nextMacroScope_1620_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_ngen_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_auxDeclNGen_1622_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_traceState_1623_);
lean_ctor_set(v_reuseFailAlloc_1641_, 5, v_cache_1624_);
lean_ctor_set(v_reuseFailAlloc_1641_, 6, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1641_, 7, v_infoState_1626_);
lean_ctor_set(v_reuseFailAlloc_1641_, 8, v_snapshotTasks_1627_);
v___x_1639_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_st_ref_put(v___y_1603_, v___x_1639_);
v_a_1582_ = v___x_1599_;
goto v___jp_1581_;
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
v___jp_1581_:
{
size_t v___x_1583_; size_t v___x_1584_; 
v___x_1583_ = ((size_t)1ULL);
v___x_1584_ = lean_usize_add(v_i_1576_, v___x_1583_);
v_i_1576_ = v___x_1584_;
v_b_1577_ = v_a_1582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v_ictx_1657_, lean_object* v___x_1658_, lean_object* v_as_1659_, lean_object* v_sz_1660_, lean_object* v_i_1661_, lean_object* v_b_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
size_t v_sz_boxed_1666_; size_t v_i_boxed_1667_; lean_object* v_res_1668_; 
v_sz_boxed_1666_ = lean_unbox_usize(v_sz_1660_);
lean_dec(v_sz_1660_);
v_i_boxed_1667_ = lean_unbox_usize(v_i_1661_);
lean_dec(v_i_1661_);
v_res_1668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v_ictx_1657_, v___x_1658_, v_as_1659_, v_sz_boxed_1666_, v_i_boxed_1667_, v_b_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v_as_1659_);
lean_dec(v___x_1658_);
return v_res_1668_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_box(1);
v___x_1670_ = l_Lean_MessageData_ofFormat(v___x_1669_);
return v___x_1670_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2));
v___x_1675_ = l_Lean_MessageData_ofFormat(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
return v_x_1676_;
}
else
{
lean_object* v_head_1678_; lean_object* v_tail_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1701_; 
v_head_1678_ = lean_ctor_get(v_x_1677_, 0);
v_tail_1679_ = lean_ctor_get(v_x_1677_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1677_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1681_ = v_x_1677_;
v_isShared_1682_ = v_isSharedCheck_1701_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_tail_1679_);
lean_inc(v_head_1678_);
lean_dec(v_x_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1701_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_before_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1699_; 
v_before_1683_ = lean_ctor_get(v_head_1678_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_head_1678_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v_head_1678_, 1);
lean_dec(v_unused_1700_);
v___x_1685_ = v_head_1678_;
v_isShared_1686_ = v_isSharedCheck_1699_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_before_1683_);
lean_dec(v_head_1678_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1699_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0);
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 7);
lean_ctor_set(v___x_1685_, 1, v___x_1687_);
lean_ctor_set(v___x_1685_, 0, v_x_1676_);
v___x_1689_ = v___x_1685_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_x_1676_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__3);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 7);
lean_ctor_set(v___x_1681_, 1, v___x_1690_);
lean_ctor_set(v___x_1681_, 0, v___x_1689_);
v___x_1692_ = v___x_1681_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = l_Lean_MessageData_ofSyntax(v_before_1683_);
v___x_1694_ = l_Lean_indentD(v___x_1693_);
v___x_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1692_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v_x_1676_ = v___x_1695_;
v_x_1677_ = v_tail_1679_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__1));
v___x_1706_ = l_Lean_MessageData_ofFormat(v___x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_msgData_1707_, lean_object* v_macroStack_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_toCold_1711_; lean_object* v_options_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v_toCold_1711_ = lean_ctor_get(v___y_1709_, 0);
v_options_1712_ = lean_ctor_get(v_toCold_1711_, 2);
v___x_1713_ = l_Lean_Elab_pp_macroStack;
v___x_1714_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1712_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v_macroStack_1708_);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_msgData_1707_);
return v___x_1715_;
}
else
{
if (lean_obj_tag(v_macroStack_1708_) == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_msgData_1707_);
return v___x_1716_;
}
else
{
lean_object* v_head_1717_; lean_object* v_after_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1733_; 
v_head_1717_ = lean_ctor_get(v_macroStack_1708_, 0);
lean_inc(v_head_1717_);
v_after_1718_ = lean_ctor_get(v_head_1717_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_head_1717_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v_head_1717_, 0);
lean_dec(v_unused_1734_);
v___x_1720_ = v_head_1717_;
v_isShared_1721_ = v_isSharedCheck_1733_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_after_1718_);
lean_dec(v_head_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1733_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0);
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 7);
lean_ctor_set(v___x_1720_, 1, v___x_1722_);
lean_ctor_set(v___x_1720_, 0, v_msgData_1707_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_msgData_1707_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v_msgData_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1725_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___closed__2);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_MessageData_ofSyntax(v_after_1718_);
v___x_1728_ = l_Lean_indentD(v___x_1727_);
v_msgData_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1729_, 0, v___x_1726_);
lean_ctor_set(v_msgData_1729_, 1, v___x_1728_);
v___x_1730_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3_spec__4(v_msgData_1729_, v_macroStack_1708_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_1735_, lean_object* v_macroStack_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg(v_msgData_1735_, v_macroStack_1736_, v___y_1737_);
lean_dec_ref(v___y_1737_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_ref_1748_; lean_object* v___x_1749_; lean_object* v_a_1750_; lean_object* v_macroStack_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1762_; 
v_ref_1748_ = lean_ctor_get(v___y_1745_, 2);
v___x_1749_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_1740_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v_macroStack_1751_ = lean_ctor_get(v___y_1741_, 1);
v___x_1752_ = l_Lean_Elab_getBetterRef(v_ref_1748_, v_macroStack_1751_);
lean_inc(v_macroStack_1751_);
v___x_1753_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg(v_a_1750_, v_macroStack_1751_, v___y_1745_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1752_);
lean_ctor_set(v___x_1758_, 1, v_a_1754_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 1);
lean_ctor_set(v___x_1756_, 0, v___x_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1772_, lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_toCold_1781_; lean_object* v_currRecDepth_1782_; lean_object* v_ref_1783_; uint8_t v_diag_1784_; uint8_t v_suppressElabErrors_1785_; lean_object* v_ref_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_toCold_1781_ = lean_ctor_get(v___y_1778_, 0);
v_currRecDepth_1782_ = lean_ctor_get(v___y_1778_, 1);
v_ref_1783_ = lean_ctor_get(v___y_1778_, 2);
v_diag_1784_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*3);
v_suppressElabErrors_1785_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*3 + 1);
v_ref_1786_ = l_Lean_replaceRef(v_ref_1772_, v_ref_1783_);
lean_inc(v_currRecDepth_1782_);
lean_inc_ref(v_toCold_1781_);
v___x_1787_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1787_, 0, v_toCold_1781_);
lean_ctor_set(v___x_1787_, 1, v_currRecDepth_1782_);
lean_ctor_set(v___x_1787_, 2, v_ref_1786_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3, v_diag_1784_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3 + 1, v_suppressElabErrors_1785_);
v___x_1788_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___x_1787_, v___y_1779_);
lean_dec_ref_known(v___x_1787_, 3);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1789_, lean_object* v_msg_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1789_, v_msg_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v_ref_1789_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_toCold_1810_; uint8_t v_suppressElabErrors_1811_; lean_object* v_fileName_1812_; lean_object* v_fileMap_1813_; lean_object* v_options_1814_; lean_object* v_currNamespace_1815_; lean_object* v_openDecls_1816_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; uint8_t v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; 
v_toCold_1810_ = lean_ctor_get(v___y_1804_, 0);
v_suppressElabErrors_1811_ = lean_ctor_get_uint8(v___y_1804_, sizeof(void*)*3 + 1);
v_fileName_1812_ = lean_ctor_get(v_toCold_1810_, 0);
v_fileMap_1813_ = lean_ctor_get(v_toCold_1810_, 1);
v_options_1814_ = lean_ctor_get(v_toCold_1810_, 2);
v_currNamespace_1815_ = lean_ctor_get(v_toCold_1810_, 4);
v_openDecls_1816_ = lean_ctor_get(v_toCold_1810_, 5);
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = l_Lean_Syntax_getArg(v_docComment_1799_, v___x_1851_);
v___x_1853_ = 1;
v___x_1854_ = l_Lean_Syntax_getPos_x3f(v___x_1852_, v___x_1853_);
if (lean_obj_tag(v___x_1854_) == 1)
{
lean_object* v_val_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1937_; 
v_val_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1937_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_val_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1937_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_Syntax_getTailPos_x3f(v___x_1852_, v___x_1853_);
lean_dec(v___x_1852_);
if (lean_obj_tag(v___x_1859_) == 1)
{
lean_object* v_val_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1934_; 
v_val_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1934_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_val_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1934_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_source_1864_; lean_object* v___y_1866_; lean_object* v___x_1930_; lean_object* v_endPos_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_source_1864_ = lean_ctor_get(v_fileMap_1813_, 0);
v___x_1930_ = lean_string_utf8_prev(v_source_1864_, v_val_1860_);
lean_dec(v_val_1860_);
v_endPos_1931_ = lean_string_utf8_prev(v_source_1864_, v___x_1930_);
lean_dec(v___x_1930_);
v___x_1932_ = lean_string_utf8_byte_size(v_source_1864_);
v___x_1933_ = lean_nat_dec_le(v_endPos_1931_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_dec(v_endPos_1931_);
v___y_1866_ = v___x_1932_;
goto v___jp_1865_;
}
else
{
v___y_1866_ = v_endPos_1931_;
goto v___jp_1865_;
}
v___jp_1865_:
{
lean_object* v___x_1867_; lean_object* v_env_1868_; lean_object* v_ictx_1869_; lean_object* v_pmctx_1870_; lean_object* v_blockCtxt_1871_; lean_object* v___x_1872_; lean_object* v_s_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_s_1876_; lean_object* v_errors_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1867_ = lean_st_ref_get(v___y_1805_);
v_env_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref_n(v_env_1868_, 2);
lean_dec(v___x_1867_);
lean_inc(v___y_1866_);
lean_inc_ref_n(v_fileMap_1813_, 2);
lean_inc_ref(v_fileName_1812_);
lean_inc_ref(v_source_1864_);
v_ictx_1869_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_1869_, 0, v_source_1864_);
lean_ctor_set(v_ictx_1869_, 1, v_fileName_1812_);
lean_ctor_set(v_ictx_1869_, 2, v_fileMap_1813_);
lean_ctor_set(v_ictx_1869_, 3, v___y_1866_);
lean_inc(v_openDecls_1816_);
lean_inc(v_currNamespace_1815_);
lean_inc_ref(v_options_1814_);
v_pmctx_1870_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_1870_, 0, v_env_1868_);
lean_ctor_set(v_pmctx_1870_, 1, v_options_1814_);
lean_ctor_set(v_pmctx_1870_, 2, v_currNamespace_1815_);
lean_ctor_set(v_pmctx_1870_, 3, v_openDecls_1816_);
lean_inc(v_val_1855_);
v_blockCtxt_1871_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_fileMap_1813_, v_val_1855_, v___y_1866_);
v___x_1872_ = l_Lean_Parser_mkParserState(v_source_1864_);
v_s_1873_ = l_Lean_Parser_ParserState_setPos(v___x_1872_, v_val_1855_);
lean_inc_ref(v_blockCtxt_1871_);
v___x_1874_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_1874_, 0, v_blockCtxt_1871_);
v___x_1875_ = l_Lean_Parser_getTokenTable(v_env_1868_);
lean_inc_ref(v___x_1875_);
lean_inc_ref(v_pmctx_1870_);
lean_inc_ref_n(v_ictx_1869_, 2);
v_s_1876_ = l_Lean_Parser_ParserFn_run(v___x_1874_, v_ictx_1869_, v_pmctx_1870_, v___x_1875_, v_s_1873_);
lean_inc_ref(v_s_1876_);
v_errors_1877_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v_ictx_1869_, v_pmctx_1870_, v___x_1875_, v_source_1864_, v_blockCtxt_1871_, v_s_1876_);
v___x_1878_ = lean_array_get_size(v_errors_1877_);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_nat_dec_eq(v___x_1878_, v___x_1879_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; size_t v_sz_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
lean_dec_ref(v_s_1876_);
lean_del_object(v___x_1862_);
lean_del_object(v___x_1857_);
v___x_1881_ = lean_box(0);
v_sz_1882_ = lean_array_size(v_errors_1877_);
v___x_1883_ = ((size_t)0ULL);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v_ictx_1869_, v___x_1878_, v_errors_1877_, v_sz_1882_, v___x_1883_, v___x_1881_, v___y_1804_, v___y_1805_);
lean_dec_ref(v_errors_1877_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1892_; 
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; 
v_unused_1893_ = lean_ctor_get(v___x_1884_, 0);
lean_dec(v_unused_1893_);
v___x_1886_ = v___x_1884_;
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
else
{
lean_dec(v___x_1884_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_box(0);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1884_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1884_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_stxStack_1902_; lean_object* v_pos_1903_; uint8_t v___x_1904_; 
lean_dec_ref(v_errors_1877_);
v_stxStack_1902_ = lean_ctor_get(v_s_1876_, 0);
lean_inc_ref(v_stxStack_1902_);
v_pos_1903_ = lean_ctor_get(v_s_1876_, 2);
lean_inc(v_pos_1903_);
lean_dec_ref(v_s_1876_);
v___x_1904_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1869_, v_pos_1903_);
lean_dec_ref_known(v_ictx_1869_, 4);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint32_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec_ref(v_stxStack_1902_);
lean_del_object(v___x_1862_);
lean_inc_ref(v_fileMap_1813_);
v___x_1905_ = l_Lean_FileMap_toPosition(v_fileMap_1813_, v_pos_1903_);
v___x_1906_ = lean_box(0);
v___x_1907_ = 2;
v___x_1908_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_1909_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__0));
v___x_1910_ = lean_string_utf8_get(v_source_1864_, v_pos_1903_);
lean_dec(v_pos_1903_);
v___x_1911_ = lean_string_push(v___x_1908_, v___x_1910_);
v___x_1912_ = lean_string_append(v___x_1909_, v___x_1911_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__1));
v___x_1914_ = lean_string_append(v___x_1912_, v___x_1913_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 3);
lean_ctor_set(v___x_1857_, 0, v___x_1914_);
v___x_1916_ = v___x_1857_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_MessageData_ofFormat(v___x_1916_);
if (v_suppressElabErrors_1811_ == 0)
{
v___y_1818_ = v___x_1905_;
v___y_1819_ = v___x_1917_;
v___y_1820_ = v___x_1908_;
v___y_1821_ = v___x_1906_;
v___y_1822_ = v___x_1904_;
v___y_1823_ = v___x_1907_;
v___y_1824_ = v___y_1804_;
v___y_1825_ = v___y_1805_;
goto v___jp_1817_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___f_1920_; uint8_t v___x_1921_; 
v___x_1918_ = lean_box(v_suppressElabErrors_1811_);
v___x_1919_ = lean_box(v___x_1904_);
v___f_1920_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1920_, 0, v___x_1918_);
lean_closure_set(v___f_1920_, 1, v___x_1919_);
lean_inc_ref(v___x_1917_);
v___x_1921_ = l_Lean_MessageData_hasTag(v___f_1920_, v___x_1917_);
if (v___x_1921_ == 0)
{
lean_dec_ref(v___x_1917_);
lean_dec_ref(v___x_1905_);
goto v___jp_1807_;
}
else
{
v___y_1818_ = v___x_1905_;
v___y_1819_ = v___x_1917_;
v___y_1820_ = v___x_1908_;
v___y_1821_ = v___x_1906_;
v___y_1822_ = v___x_1904_;
v___y_1823_ = v___x_1907_;
v___y_1824_ = v___y_1804_;
v___y_1825_ = v___y_1805_;
goto v___jp_1817_;
}
}
}
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
lean_dec(v_pos_1903_);
v___x_1923_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1902_);
lean_dec_ref(v_stxStack_1902_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1923_);
v___x_1925_ = v___x_1862_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1927_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1925_);
v___x_1927_ = v___x_1857_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec(v___x_1859_);
lean_del_object(v___x_1857_);
lean_dec(v_val_1855_);
v___x_1935_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__10___closed__1, &l_Lean_parseVersoDocString___redArg___lam__10___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__10___closed__1);
v___x_1936_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1799_, v___x_1935_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
return v___x_1936_;
}
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec(v___x_1854_);
lean_dec(v___x_1852_);
v___x_1938_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__10___closed__1, &l_Lean_parseVersoDocString___redArg___lam__10___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__10___closed__1);
v___x_1939_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1799_, v___x_1938_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
return v___x_1939_;
}
v___jp_1807_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
v___jp_1817_:
{
lean_object* v___x_1826_; lean_object* v_toCold_1827_; lean_object* v_currNamespace_1828_; lean_object* v_openDecls_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_env_1833_; lean_object* v_nextMacroScope_1834_; lean_object* v_ngen_1835_; lean_object* v_auxDeclNGen_1836_; lean_object* v_traceState_1837_; lean_object* v_cache_1838_; lean_object* v_messages_1839_; lean_object* v_infoState_1840_; lean_object* v_snapshotTasks_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1850_; 
v___x_1826_ = lean_st_ref_take(v___y_1825_);
v_toCold_1827_ = lean_ctor_get(v___y_1824_, 0);
v_currNamespace_1828_ = lean_ctor_get(v_toCold_1827_, 4);
v_openDecls_1829_ = lean_ctor_get(v_toCold_1827_, 5);
lean_inc(v_openDecls_1829_);
lean_inc(v_currNamespace_1828_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_currNamespace_1828_);
lean_ctor_set(v___x_1830_, 1, v_openDecls_1829_);
v___x_1831_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set(v___x_1831_, 1, v___y_1819_);
lean_inc(v___y_1821_);
lean_inc_ref(v_fileName_1812_);
v___x_1832_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1832_, 0, v_fileName_1812_);
lean_ctor_set(v___x_1832_, 1, v___y_1818_);
lean_ctor_set(v___x_1832_, 2, v___y_1821_);
lean_ctor_set(v___x_1832_, 3, v___y_1820_);
lean_ctor_set(v___x_1832_, 4, v___x_1831_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*5, v___y_1822_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*5 + 1, v___y_1823_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*5 + 2, v___y_1822_);
v_env_1833_ = lean_ctor_get(v___x_1826_, 0);
v_nextMacroScope_1834_ = lean_ctor_get(v___x_1826_, 1);
v_ngen_1835_ = lean_ctor_get(v___x_1826_, 2);
v_auxDeclNGen_1836_ = lean_ctor_get(v___x_1826_, 3);
v_traceState_1837_ = lean_ctor_get(v___x_1826_, 4);
v_cache_1838_ = lean_ctor_get(v___x_1826_, 5);
v_messages_1839_ = lean_ctor_get(v___x_1826_, 6);
v_infoState_1840_ = lean_ctor_get(v___x_1826_, 7);
v_snapshotTasks_1841_ = lean_ctor_get(v___x_1826_, 8);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1843_ = v___x_1826_;
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_snapshotTasks_1841_);
lean_inc(v_infoState_1840_);
lean_inc(v_messages_1839_);
lean_inc(v_cache_1838_);
lean_inc(v_traceState_1837_);
lean_inc(v_auxDeclNGen_1836_);
lean_inc(v_ngen_1835_);
lean_inc(v_nextMacroScope_1834_);
lean_inc(v_env_1833_);
lean_dec(v___x_1826_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1845_ = l_Lean_MessageLog_add(v___x_1832_, v_messages_1839_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 6, v___x_1845_);
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_env_1833_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_nextMacroScope_1834_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_ngen_1835_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v_auxDeclNGen_1836_);
lean_ctor_set(v_reuseFailAlloc_1849_, 4, v_traceState_1837_);
lean_ctor_set(v_reuseFailAlloc_1849_, 5, v_cache_1838_);
lean_ctor_set(v_reuseFailAlloc_1849_, 6, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1849_, 7, v_infoState_1840_);
lean_ctor_set(v_reuseFailAlloc_1849_, 8, v_snapshotTasks_1841_);
v___x_1847_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_st_ref_put(v___y_1825_, v___x_1847_);
goto v___jp_1807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v_docComment_1940_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1957_, lean_object* v_binders_1958_, lean_object* v_docComment_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v_body_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = lean_unsigned_to_nat(1u);
v_body_1968_ = l_Lean_Syntax_getArg(v_docComment_1959_, v___x_1967_);
v___x_1969_ = 1;
v___x_1970_ = l_Lean_Syntax_getPos_x3f(v_body_1968_, v___x_1969_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_versoDocString___closed__3));
lean_inc(v_body_1968_);
v___x_1972_ = l_Lean_Syntax_isOfKind(v_body_1968_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec(v_body_1968_);
v___x_1973_ = l_Lean_TSyntax_getDocString(v_docComment_1959_);
v___x_1974_ = l_Lean_versoDocStringOfText(v_declName_1957_, v_binders_1958_, v___x_1973_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_VersoDocstringView_of(v_body_1968_);
lean_dec(v_body_1968_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_doc_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_doc_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_doc_1976_);
lean_dec_ref_known(v___x_1975_, 1);
v___x_1977_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1976_);
lean_dec(v_doc_1976_);
v___x_1978_ = lean_box(0);
v___x_1979_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1957_, v_binders_1958_, v___x_1977_, v___x_1978_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_1979_;
}
else
{
lean_object* v_text_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_text_1980_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_text_1980_);
lean_dec_ref_known(v___x_1975_, 1);
v___x_1981_ = l_Lean_Syntax_getAtomVal(v_text_1980_);
lean_dec(v_text_1980_);
v___x_1982_ = l_Lean_versoDocStringOfText(v_declName_1957_, v_binders_1958_, v___x_1981_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_1982_;
}
}
}
else
{
lean_object* v___x_1983_; 
lean_dec_ref_known(v___x_1970_, 1);
lean_dec(v_body_1968_);
v___x_1983_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2031_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_2031_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2031_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
if (lean_obj_tag(v_a_1984_) == 1)
{
lean_object* v_val_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; 
lean_del_object(v___x_1986_);
v_val_1988_ = lean_ctor_get(v_a_1984_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v_a_1984_, 1);
v___x_1989_ = l_Lean_TSyntax_getVersoBlocks(v_val_1988_);
lean_dec(v_val_1988_);
v___x_1990_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1990_, 0, v___x_1989_);
v___x_1991_ = 0;
v___x_1992_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1957_, v_binders_1958_, v___x_1990_, v___x_1991_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2018_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2018_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2018_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_fst_1997_; lean_object* v_snd_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2017_; 
v_fst_1997_ = lean_ctor_get(v_a_1993_, 0);
v_snd_1998_ = lean_ctor_get(v_a_1993_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_a_1993_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2000_ = v_a_1993_;
v_isShared_2001_ = v_isSharedCheck_2017_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_snd_1998_);
lean_inc(v_fst_1997_);
lean_dec(v_a_1993_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2017_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2016_; 
v_fst_2002_ = lean_ctor_get(v_fst_1997_, 0);
v_snd_2003_ = lean_ctor_get(v_fst_1997_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_fst_1997_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2005_ = v_fst_1997_;
v_isShared_2006_ = v_isSharedCheck_2016_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2002_);
lean_dec(v_fst_1997_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2016_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_fst_2002_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_snd_2003_);
v___x_2008_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2008_);
v___x_2010_ = v___x_2000_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_snd_1998_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2010_);
v___x_2012_ = v___x_1995_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_a_2019_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1992_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1992_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
lean_dec(v_a_1984_);
lean_dec(v_binders_1958_);
lean_dec(v_declName_1957_);
v___x_2027_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_2027_);
v___x_2029_ = v___x_1986_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_binders_1958_);
lean_dec(v_declName_1957_);
v_a_2032_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1983_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1983_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_2040_, lean_object* v_binders_2041_, lean_object* v_docComment_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_versoDocString(v_declName_2040_, v_binders_2041_, v_docComment_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_docComment_2042_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v_ictx_2051_, lean_object* v___x_2052_, lean_object* v_as_2053_, size_t v_sz_2054_, size_t v_i_2055_, lean_object* v_b_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v_ictx_2051_, v___x_2052_, v_as_2053_, v_sz_2054_, v_i_2055_, v_b_2056_, v___y_2061_, v___y_2062_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v_ictx_2065_, lean_object* v___x_2066_, lean_object* v_as_2067_, lean_object* v_sz_2068_, lean_object* v_i_2069_, lean_object* v_b_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
size_t v_sz_boxed_2078_; size_t v_i_boxed_2079_; lean_object* v_res_2080_; 
v_sz_boxed_2078_ = lean_unbox_usize(v_sz_2068_);
lean_dec(v_sz_2068_);
v_i_boxed_2079_ = lean_unbox_usize(v_i_2069_);
lean_dec(v_i_2069_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v_ictx_2065_, v___x_2066_, v_as_2067_, v_sz_boxed_2078_, v_i_boxed_2079_, v_b_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v_as_2067_);
lean_dec(v___x_2066_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_2081_, lean_object* v_ref_2082_, lean_object* v_msg_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_2082_, v_msg_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2092_, lean_object* v_ref_2093_, lean_object* v_msg_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_2092_, v_ref_2093_, v_msg_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v_ref_2093_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2103_, lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_msg_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_2113_, v_msg_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3(lean_object* v_msgData_2123_, lean_object* v_macroStack_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___redArg(v_msgData_2123_, v_macroStack_2124_, v___y_2129_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msgData_2133_, lean_object* v_macroStack_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3(v_msgData_2133_, v_macroStack_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_2143_, lean_object* v_doc_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v_val_2160_; lean_object* v_env_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2152_ = lean_st_ref_get(v_a_2150_);
v_env_2162_ = lean_ctor_get(v___x_2152_, 0);
lean_inc_ref(v_env_2162_);
lean_dec(v___x_2152_);
v___x_2163_ = l_Lean_getMainVersoModuleDocs(v_env_2162_);
v___x_2164_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_2163_);
lean_dec_ref(v___x_2163_);
if (lean_obj_tag(v___x_2164_) == 0)
{
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2144_);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___y_2154_ = v___x_2165_;
v___y_2155_ = v___x_2166_;
goto v___jp_2153_;
}
else
{
lean_object* v_val_2167_; 
v_val_2167_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_val_2167_);
lean_dec_ref_known(v___x_2164_, 1);
v_val_2160_ = v_val_2167_;
goto v___jp_2159_;
}
}
else
{
lean_object* v_val_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_val_2168_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_val_2168_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2169_ = lean_unsigned_to_nat(1u);
v___x_2170_ = lean_nat_add(v_val_2168_, v___x_2169_);
lean_dec(v_val_2168_);
v_val_2160_ = v___x_2170_;
goto v___jp_2159_;
}
v___jp_2153_:
{
lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_2156_, 0, v_range_2143_);
lean_closure_set(v___x_2156_, 1, v___y_2154_);
lean_closure_set(v___x_2156_, 2, v___y_2155_);
v___x_2157_ = 0;
v___x_2158_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_2156_, v___x_2157_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
return v___x_2158_;
}
v___jp_2159_:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2144_);
v___y_2154_ = v___x_2161_;
v___y_2155_ = v_val_2160_;
goto v___jp_2153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_2171_, lean_object* v_doc_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_versoModDocString(v_range_2171_, v_doc_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_doc_2172_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2190_, lean_object* v_docComment_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_2200_ = l_Lean_versoDocStringOfText(v_declName_2190_, v___x_2199_, v_docComment_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2201_, lean_object* v_docComment_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_versoDocStringFromString(v_declName_2201_, v_docComment_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2211_, lean_object* v_declName_2212_, lean_object* v_env_2213_){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = l_Lean_docStringExt;
v___x_2215_ = l_String_removeLeadingSpaces(v_docString_2211_);
v___x_2216_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2214_, v_env_2213_, v_declName_2212_, v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2217_, lean_object* v_modifyEnv_2218_, lean_object* v_docString_2219_){
_start:
{
lean_object* v___f_2220_; lean_object* v___x_2221_; 
v___f_2220_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2220_, 0, v_docString_2219_);
lean_closure_set(v___f_2220_, 1, v_declName_2217_);
v___x_2221_ = lean_apply_1(v_modifyEnv_2218_, v___f_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_docComment_2224_, lean_object* v_toBind_2225_, lean_object* v___f_2226_, lean_object* v_____r_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = l_Lean_getDocStringText___redArg(v_inst_2222_, v_inst_2223_, v_docComment_2224_);
v___x_2229_ = lean_apply_4(v_toBind_2225_, lean_box(0), lean_box(0), v___x_2228_, v___f_2226_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2230_, lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_inst_2233_, lean_object* v_inst_2234_, lean_object* v_docComment_2235_, lean_object* v_toBind_2236_, lean_object* v___f_2237_, lean_object* v_____r_2238_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = l_Lean_validateDocComment___redArg(v_inst_2230_, v_inst_2231_, v_inst_2232_, v_inst_2233_, v_inst_2234_, v_docComment_2235_);
v___x_2240_ = lean_apply_4(v_toBind_2236_, lean_box(0), lean_box(0), v___x_2239_, v___f_2237_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_docComment_2246_, lean_object* v_toBind_2247_, lean_object* v___f_2248_, lean_object* v_____r_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2241_, v_inst_2242_, v_inst_2243_, v_inst_2244_, v_inst_2245_, v_docComment_2246_, v_toBind_2247_, v___f_2248_, v_____r_2249_);
lean_dec(v_docComment_2246_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2251_, lean_object* v_____r_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_apply_1(v___f_2251_, v_____r_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2260_, lean_object* v_declName_2261_, uint8_t v___x_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_toBind_2265_, lean_object* v___f_2266_, lean_object* v_____do__lift_2267_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2267_, v_declName_2261_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_dec(v___f_2266_);
lean_dec(v_toBind_2265_);
lean_dec_ref(v_inst_2264_);
lean_dec_ref(v_inst_2263_);
lean_dec(v_declName_2261_);
goto v___jp_2268_;
}
else
{
lean_dec_ref_known(v___x_2271_, 1);
if (v___x_2262_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec(v___f_2260_);
v___x_2272_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2273_ = l_Lean_MessageData_ofConstName(v_declName_2261_, v___x_2262_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_throwError___redArg(v_inst_2263_, v_inst_2264_, v___x_2276_);
v___x_2278_ = lean_apply_4(v_toBind_2265_, lean_box(0), lean_box(0), v___x_2277_, v___f_2266_);
return v___x_2278_;
}
else
{
lean_dec(v___f_2266_);
lean_dec(v_toBind_2265_);
lean_dec_ref(v_inst_2264_);
lean_dec_ref(v_inst_2263_);
lean_dec(v_declName_2261_);
goto v___jp_2268_;
}
}
v___jp_2268_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_apply_1(v___f_2260_, v___x_2269_);
return v___x_2270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2279_, lean_object* v_declName_2280_, lean_object* v___x_2281_, lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_toBind_2284_, lean_object* v___f_2285_, lean_object* v_____do__lift_2286_){
_start:
{
uint8_t v___x_243__boxed_2287_; lean_object* v_res_2288_; 
v___x_243__boxed_2287_ = lean_unbox(v___x_2281_);
v_res_2288_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2279_, v_declName_2280_, v___x_243__boxed_2287_, v_inst_2282_, v_inst_2283_, v_toBind_2284_, v___f_2285_, v_____do__lift_2286_);
lean_dec_ref(v_____do__lift_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_declName_2296_, lean_object* v_docComment_2297_){
_start:
{
lean_object* v_toApplicative_2298_; lean_object* v_toBind_2299_; lean_object* v_toPure_2300_; uint8_t v___x_2301_; 
v_toApplicative_2298_ = lean_ctor_get(v_inst_2289_, 0);
v_toBind_2299_ = lean_ctor_get(v_inst_2289_, 1);
lean_inc(v_toBind_2299_);
v_toPure_2300_ = lean_ctor_get(v_toApplicative_2298_, 1);
v___x_2301_ = l_Lean_Name_isAnonymous(v_declName_2296_);
if (v___x_2301_ == 0)
{
lean_object* v_getEnv_2302_; lean_object* v_modifyEnv_2303_; lean_object* v___f_2304_; lean_object* v___f_2305_; lean_object* v___f_2306_; lean_object* v___f_2307_; lean_object* v___x_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; 
v_getEnv_2302_ = lean_ctor_get(v_inst_2292_, 0);
lean_inc(v_getEnv_2302_);
v_modifyEnv_2303_ = lean_ctor_get(v_inst_2292_, 1);
lean_inc(v_modifyEnv_2303_);
lean_dec_ref(v_inst_2292_);
lean_inc(v_declName_2296_);
v___f_2304_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2304_, 0, v_declName_2296_);
lean_closure_set(v___f_2304_, 1, v_modifyEnv_2303_);
lean_inc_n(v_toBind_2299_, 3);
lean_inc(v_docComment_2297_);
lean_inc_ref(v_inst_2293_);
lean_inc_ref_n(v_inst_2289_, 2);
v___f_2305_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2305_, 0, v_inst_2289_);
lean_closure_set(v___f_2305_, 1, v_inst_2293_);
lean_closure_set(v___f_2305_, 2, v_docComment_2297_);
lean_closure_set(v___f_2305_, 3, v_toBind_2299_);
lean_closure_set(v___f_2305_, 4, v___f_2304_);
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2306_, 0, v_inst_2289_);
lean_closure_set(v___f_2306_, 1, v_inst_2290_);
lean_closure_set(v___f_2306_, 2, v_inst_2294_);
lean_closure_set(v___f_2306_, 3, v_inst_2295_);
lean_closure_set(v___f_2306_, 4, v_inst_2291_);
lean_closure_set(v___f_2306_, 5, v_docComment_2297_);
lean_closure_set(v___f_2306_, 6, v_toBind_2299_);
lean_closure_set(v___f_2306_, 7, v___f_2305_);
lean_inc_ref(v___f_2306_);
v___f_2307_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2307_, 0, v___f_2306_);
v___x_2308_ = lean_box(v___x_2301_);
v___f_2309_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2309_, 0, v___f_2306_);
lean_closure_set(v___f_2309_, 1, v_declName_2296_);
lean_closure_set(v___f_2309_, 2, v___x_2308_);
lean_closure_set(v___f_2309_, 3, v_inst_2289_);
lean_closure_set(v___f_2309_, 4, v_inst_2293_);
lean_closure_set(v___f_2309_, 5, v_toBind_2299_);
lean_closure_set(v___f_2309_, 6, v___f_2307_);
v___x_2310_ = lean_apply_4(v_toBind_2299_, lean_box(0), lean_box(0), v_getEnv_2302_, v___f_2309_);
return v___x_2310_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_inc(v_toPure_2300_);
lean_dec(v_toBind_2299_);
lean_dec(v_docComment_2297_);
lean_dec(v_declName_2296_);
lean_dec(v_inst_2295_);
lean_dec_ref(v_inst_2294_);
lean_dec_ref(v_inst_2293_);
lean_dec_ref(v_inst_2292_);
lean_dec(v_inst_2291_);
lean_dec(v_inst_2290_);
lean_dec_ref(v_inst_2289_);
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_apply_2(v_toPure_2300_, lean_box(0), v___x_2311_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2313_, lean_object* v_inst_2314_, lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_, lean_object* v_inst_2319_, lean_object* v_inst_2320_, lean_object* v_declName_2321_, lean_object* v_docComment_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_addMarkdownDocString___redArg(v_inst_2314_, v_inst_2315_, v_inst_2316_, v_inst_2317_, v_inst_2318_, v_inst_2319_, v_inst_2320_, v_declName_2321_, v_docComment_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2324_, lean_object* v_x1_2325_, lean_object* v_x2_2326_){
_start:
{
lean_object* v_index_2327_; lean_object* v_sourceString_2328_; lean_object* v_imports_2329_; lean_object* v_currNamespace_2330_; lean_object* v_openDecls_2331_; lean_object* v_options_2332_; lean_object* v_check_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2346_; 
v_index_2327_ = lean_ctor_get(v_x2_2326_, 1);
v_sourceString_2328_ = lean_ctor_get(v_x2_2326_, 2);
v_imports_2329_ = lean_ctor_get(v_x2_2326_, 3);
v_currNamespace_2330_ = lean_ctor_get(v_x2_2326_, 4);
v_openDecls_2331_ = lean_ctor_get(v_x2_2326_, 5);
v_options_2332_ = lean_ctor_get(v_x2_2326_, 6);
v_check_2333_ = lean_ctor_get(v_x2_2326_, 7);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_x2_2326_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v_x2_2326_, 0);
lean_dec(v_unused_2347_);
v___x_2335_ = v_x2_2326_;
v_isShared_2336_ = v_isSharedCheck_2346_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_check_2333_);
lean_inc(v_options_2332_);
lean_inc(v_openDecls_2331_);
lean_inc(v_currNamespace_2330_);
lean_inc(v_imports_2329_);
lean_inc(v_sourceString_2328_);
lean_inc(v_index_2327_);
lean_dec(v_x2_2326_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2346_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v_toEnvExtension_2338_; lean_object* v_asyncMode_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2337_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2338_ = lean_ctor_get(v___x_2337_, 0);
v_asyncMode_2339_ = lean_ctor_get(v_toEnvExtension_2338_, 2);
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v_declName_2324_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2340_);
v___x_2342_ = v___x_2335_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_index_2327_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_sourceString_2328_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_imports_2329_);
lean_ctor_set(v_reuseFailAlloc_2345_, 4, v_currNamespace_2330_);
lean_ctor_set(v_reuseFailAlloc_2345_, 5, v_openDecls_2331_);
lean_ctor_set(v_reuseFailAlloc_2345_, 6, v_options_2332_);
lean_ctor_set(v_reuseFailAlloc_2345_, 7, v_check_2333_);
v___x_2342_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2337_, v_x1_2325_, v___x_2342_, v_asyncMode_2339_, v___x_2343_);
return v___x_2344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_2367_, lean_object* v_docs_2368_, lean_object* v_deferred_2369_, lean_object* v___f_2370_, lean_object* v_env_2371_){
_start:
{
lean_object* v___x_2372_; lean_object* v_env_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2372_ = l_Lean_versoDocStringExt;
v_env_2373_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2372_, v_env_2371_, v_declName_2367_, v_docs_2368_);
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = lean_array_get_size(v_deferred_2369_);
v___x_2376_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2377_ = lean_nat_dec_lt(v___x_2374_, v___x_2375_);
if (v___x_2377_ == 0)
{
lean_dec_ref(v___f_2370_);
lean_dec_ref(v_deferred_2369_);
return v_env_2373_;
}
else
{
uint8_t v___x_2378_; 
v___x_2378_ = lean_nat_dec_le(v___x_2375_, v___x_2375_);
if (v___x_2378_ == 0)
{
if (v___x_2377_ == 0)
{
lean_dec_ref(v___f_2370_);
lean_dec_ref(v_deferred_2369_);
return v_env_2373_;
}
else
{
size_t v___x_2379_; size_t v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = ((size_t)0ULL);
v___x_2380_ = lean_usize_of_nat(v___x_2375_);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2376_, v___f_2370_, v_deferred_2369_, v___x_2379_, v___x_2380_, v_env_2373_);
return v___x_2381_;
}
}
else
{
size_t v___x_2382_; size_t v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = ((size_t)0ULL);
v___x_2383_ = lean_usize_of_nat(v___x_2375_);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2376_, v___f_2370_, v_deferred_2369_, v___x_2382_, v___x_2383_, v_env_2373_);
return v___x_2384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_2385_, lean_object* v___f_2386_, lean_object* v_____r_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_apply_1(v_modifyEnv_2385_, v___f_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_2391_, lean_object* v_modifyEnv_2392_, lean_object* v___f_2393_, uint8_t v___x_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_toBind_2397_, lean_object* v___f_2398_, lean_object* v_____do__lift_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2399_, v_declName_2391_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v___x_2401_; 
lean_dec(v___f_2398_);
lean_dec(v_toBind_2397_);
lean_dec_ref(v_inst_2396_);
lean_dec_ref(v_inst_2395_);
lean_dec(v_declName_2391_);
v___x_2401_ = lean_apply_1(v_modifyEnv_2392_, v___f_2393_);
return v___x_2401_;
}
else
{
lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2418_; 
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; 
v_unused_2419_ = lean_ctor_get(v___x_2400_, 0);
lean_dec(v_unused_2419_);
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2418_;
goto v_resetjp_2402_;
}
else
{
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2418_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
if (v___x_2394_ == 0)
{
lean_object* v___x_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
lean_dec_ref(v___f_2393_);
lean_dec(v_modifyEnv_2392_);
v___x_2405_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2406_ = 1;
v___x_2407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2391_, v___x_2406_);
v___x_2408_ = lean_string_append(v___x_2405_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2410_ = lean_string_append(v___x_2408_, v___x_2409_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 3);
lean_ctor_set(v___x_2403_, 0, v___x_2410_);
v___x_2412_ = v___x_2403_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = l_Lean_MessageData_ofFormat(v___x_2412_);
v___x_2414_ = l_Lean_throwError___redArg(v_inst_2395_, v_inst_2396_, v___x_2413_);
v___x_2415_ = lean_apply_4(v_toBind_2397_, lean_box(0), lean_box(0), v___x_2414_, v___f_2398_);
return v___x_2415_;
}
}
else
{
lean_object* v___x_2417_; 
lean_del_object(v___x_2403_);
lean_dec(v___f_2398_);
lean_dec(v_toBind_2397_);
lean_dec_ref(v_inst_2396_);
lean_dec_ref(v_inst_2395_);
lean_dec(v_declName_2391_);
v___x_2417_ = lean_apply_1(v_modifyEnv_2392_, v___f_2393_);
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_2420_, lean_object* v_modifyEnv_2421_, lean_object* v___f_2422_, lean_object* v___x_2423_, lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_toBind_2426_, lean_object* v___f_2427_, lean_object* v_____do__lift_2428_){
_start:
{
uint8_t v___x_371__boxed_2429_; lean_object* v_res_2430_; 
v___x_371__boxed_2429_ = lean_unbox(v___x_2423_);
v_res_2430_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_2420_, v_modifyEnv_2421_, v___f_2422_, v___x_371__boxed_2429_, v_inst_2424_, v_inst_2425_, v_toBind_2426_, v___f_2427_, v_____do__lift_2428_);
lean_dec_ref(v_____do__lift_2428_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_declName_2434_, lean_object* v_docs_2435_, lean_object* v_deferred_2436_){
_start:
{
lean_object* v_toApplicative_2437_; lean_object* v_toBind_2438_; lean_object* v_toPure_2439_; uint8_t v___x_2440_; 
v_toApplicative_2437_ = lean_ctor_get(v_inst_2431_, 0);
v_toBind_2438_ = lean_ctor_get(v_inst_2431_, 1);
lean_inc(v_toBind_2438_);
v_toPure_2439_ = lean_ctor_get(v_toApplicative_2437_, 1);
v___x_2440_ = l_Lean_Name_isAnonymous(v_declName_2434_);
if (v___x_2440_ == 0)
{
lean_object* v_getEnv_2441_; lean_object* v_modifyEnv_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; 
v_getEnv_2441_ = lean_ctor_get(v_inst_2432_, 0);
lean_inc(v_getEnv_2441_);
v_modifyEnv_2442_ = lean_ctor_get(v_inst_2432_, 1);
lean_inc_n(v_modifyEnv_2442_, 2);
lean_dec_ref(v_inst_2432_);
lean_inc_n(v_declName_2434_, 2);
v___f_2443_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2443_, 0, v_declName_2434_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2444_, 0, v_declName_2434_);
lean_closure_set(v___f_2444_, 1, v_docs_2435_);
lean_closure_set(v___f_2444_, 2, v_deferred_2436_);
lean_closure_set(v___f_2444_, 3, v___f_2443_);
lean_inc_ref(v___f_2444_);
v___f_2445_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2445_, 0, v_modifyEnv_2442_);
lean_closure_set(v___f_2445_, 1, v___f_2444_);
v___x_2446_ = lean_box(v___x_2440_);
lean_inc(v_toBind_2438_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2447_, 0, v_declName_2434_);
lean_closure_set(v___f_2447_, 1, v_modifyEnv_2442_);
lean_closure_set(v___f_2447_, 2, v___f_2444_);
lean_closure_set(v___f_2447_, 3, v___x_2446_);
lean_closure_set(v___f_2447_, 4, v_inst_2431_);
lean_closure_set(v___f_2447_, 5, v_inst_2433_);
lean_closure_set(v___f_2447_, 6, v_toBind_2438_);
lean_closure_set(v___f_2447_, 7, v___f_2445_);
v___x_2448_ = lean_apply_4(v_toBind_2438_, lean_box(0), lean_box(0), v_getEnv_2441_, v___f_2447_);
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_inc(v_toPure_2439_);
lean_dec(v_toBind_2438_);
lean_dec_ref(v_deferred_2436_);
lean_dec_ref(v_docs_2435_);
lean_dec(v_declName_2434_);
lean_dec_ref(v_inst_2433_);
lean_dec_ref(v_inst_2432_);
lean_dec_ref(v_inst_2431_);
v___x_2449_ = lean_box(0);
v___x_2450_ = lean_apply_2(v_toPure_2439_, lean_box(0), v___x_2449_);
return v___x_2450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2451_, lean_object* v_inst_2452_, lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_declName_2456_, lean_object* v_docs_2457_, lean_object* v_deferred_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2452_, v_inst_2453_, v_inst_2455_, v_declName_2456_, v_docs_2457_, v_deferred_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_declName_2465_, lean_object* v_docs_2466_, lean_object* v_deferred_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_addVersoDocStringCore(v_m_2460_, v_inst_2461_, v_inst_2462_, v_inst_2463_, v_inst_2464_, v_declName_2465_, v_docs_2466_, v_deferred_2467_);
lean_dec(v_inst_2463_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_2469_, lean_object* v_x1_2470_, lean_object* v_x2_2471_){
_start:
{
lean_object* v_index_2472_; lean_object* v_sourceString_2473_; lean_object* v_imports_2474_; lean_object* v_currNamespace_2475_; lean_object* v_openDecls_2476_; lean_object* v_options_2477_; lean_object* v_check_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2491_; 
v_index_2472_ = lean_ctor_get(v_x2_2471_, 1);
v_sourceString_2473_ = lean_ctor_get(v_x2_2471_, 2);
v_imports_2474_ = lean_ctor_get(v_x2_2471_, 3);
v_currNamespace_2475_ = lean_ctor_get(v_x2_2471_, 4);
v_openDecls_2476_ = lean_ctor_get(v_x2_2471_, 5);
v_options_2477_ = lean_ctor_get(v_x2_2471_, 6);
v_check_2478_ = lean_ctor_get(v_x2_2471_, 7);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_x2_2471_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v_x2_2471_, 0);
lean_dec(v_unused_2492_);
v___x_2480_ = v_x2_2471_;
v_isShared_2481_ = v_isSharedCheck_2491_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_check_2478_);
lean_inc(v_options_2477_);
lean_inc(v_openDecls_2476_);
lean_inc(v_currNamespace_2475_);
lean_inc(v_imports_2474_);
lean_inc(v_sourceString_2473_);
lean_inc(v_index_2472_);
lean_dec(v_x2_2471_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2491_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v_toEnvExtension_2483_; lean_object* v_asyncMode_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2482_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2483_ = lean_ctor_get(v___x_2482_, 0);
v_asyncMode_2484_ = lean_ctor_get(v_toEnvExtension_2483_, 2);
v___x_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_size_2469_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2485_);
v___x_2487_ = v___x_2480_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_index_2472_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_sourceString_2473_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_imports_2474_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v_currNamespace_2475_);
lean_ctor_set(v_reuseFailAlloc_2490_, 5, v_openDecls_2476_);
lean_ctor_set(v_reuseFailAlloc_2490_, 6, v_options_2477_);
lean_ctor_set(v_reuseFailAlloc_2490_, 7, v_check_2478_);
v___x_2487_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_box(0);
v___x_2489_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2482_, v_x1_2470_, v___x_2487_, v_asyncMode_2484_, v___x_2488_);
return v___x_2489_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2495_ = l_Lean_stringToMessageData(v___x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_deferred_2499_, lean_object* v_inst_2500_, lean_object* v___f_2501_, lean_object* v_____do__lift_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2502_, v_docs_2496_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec_ref(v___f_2501_);
lean_dec_ref(v_inst_2500_);
lean_dec_ref(v_deferred_2499_);
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2506_ = l_Lean_stringToMessageData(v_a_2504_);
v___x_2507_ = l_Lean_indentD(v___x_2506_);
v___x_2508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2505_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = l_Lean_throwError___redArg(v_inst_2497_, v_inst_2498_, v___x_2508_);
return v___x_2509_;
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
lean_dec_ref(v_inst_2498_);
lean_dec_ref(v_inst_2497_);
v_a_2510_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2510_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = lean_array_get_size(v_deferred_2499_);
v___x_2513_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2514_ = lean_nat_dec_lt(v___x_2511_, v___x_2512_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
lean_dec_ref(v___f_2501_);
lean_dec_ref(v_deferred_2499_);
v___x_2515_ = l_Lean_setEnv___redArg(v_inst_2500_, v_a_2510_);
return v___x_2515_;
}
else
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_nat_dec_le(v___x_2512_, v___x_2512_);
if (v___x_2516_ == 0)
{
if (v___x_2514_ == 0)
{
lean_object* v___x_2517_; 
lean_dec_ref(v___f_2501_);
lean_dec_ref(v_deferred_2499_);
v___x_2517_ = l_Lean_setEnv___redArg(v_inst_2500_, v_a_2510_);
return v___x_2517_;
}
else
{
size_t v___x_2518_; size_t v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2518_ = ((size_t)0ULL);
v___x_2519_ = lean_usize_of_nat(v___x_2512_);
v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2513_, v___f_2501_, v_deferred_2499_, v___x_2518_, v___x_2519_, v_a_2510_);
v___x_2521_ = l_Lean_setEnv___redArg(v_inst_2500_, v___x_2520_);
return v___x_2521_;
}
}
else
{
size_t v___x_2522_; size_t v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = lean_usize_of_nat(v___x_2512_);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2513_, v___f_2501_, v_deferred_2499_, v___x_2522_, v___x_2523_, v_a_2510_);
v___x_2525_ = l_Lean_setEnv___redArg(v_inst_2500_, v___x_2524_);
return v___x_2525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_2526_, lean_object* v_inst_2527_, lean_object* v_inst_2528_, lean_object* v_deferred_2529_, lean_object* v_inst_2530_, lean_object* v_toBind_2531_, lean_object* v_getEnv_2532_, lean_object* v_____do__lift_2533_){
_start:
{
lean_object* v___x_2534_; lean_object* v_size_2535_; lean_object* v___f_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; 
v___x_2534_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2533_);
v_size_2535_ = lean_ctor_get(v___x_2534_, 2);
lean_inc(v_size_2535_);
lean_dec_ref(v___x_2534_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2536_, 0, v_size_2535_);
v___f_2537_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2537_, 0, v_docs_2526_);
lean_closure_set(v___f_2537_, 1, v_inst_2527_);
lean_closure_set(v___f_2537_, 2, v_inst_2528_);
lean_closure_set(v___f_2537_, 3, v_deferred_2529_);
lean_closure_set(v___f_2537_, 4, v_inst_2530_);
lean_closure_set(v___f_2537_, 5, v___f_2536_);
v___x_2538_ = lean_apply_4(v_toBind_2531_, lean_box(0), lean_box(0), v_getEnv_2532_, v___f_2537_);
return v___x_2538_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2541_ = l_Lean_stringToMessageData(v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_toBind_2544_, lean_object* v_getEnv_2545_, lean_object* v___f_2546_, lean_object* v_____do__lift_2547_){
_start:
{
lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = l_Lean_getMainModuleDoc(v_____do__lift_2547_);
v___x_2549_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2548_);
lean_dec_ref(v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v___f_2546_);
lean_dec(v_getEnv_2545_);
lean_dec(v_toBind_2544_);
v___x_2550_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2551_ = l_Lean_throwError___redArg(v_inst_2542_, v_inst_2543_, v___x_2550_);
return v___x_2551_;
}
else
{
lean_object* v___x_2552_; 
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_inst_2542_);
v___x_2552_ = lean_apply_4(v_toBind_2544_, lean_box(0), lean_box(0), v_getEnv_2545_, v___f_2546_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_inst_2555_, lean_object* v_docs_2556_, lean_object* v_deferred_2557_){
_start:
{
lean_object* v_toBind_2558_; lean_object* v_getEnv_2559_; lean_object* v___f_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; 
v_toBind_2558_ = lean_ctor_get(v_inst_2553_, 1);
lean_inc_n(v_toBind_2558_, 3);
v_getEnv_2559_ = lean_ctor_get(v_inst_2554_, 0);
lean_inc_n(v_getEnv_2559_, 3);
lean_inc_ref(v_inst_2555_);
lean_inc_ref(v_inst_2553_);
v___f_2560_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2560_, 0, v_docs_2556_);
lean_closure_set(v___f_2560_, 1, v_inst_2553_);
lean_closure_set(v___f_2560_, 2, v_inst_2555_);
lean_closure_set(v___f_2560_, 3, v_deferred_2557_);
lean_closure_set(v___f_2560_, 4, v_inst_2554_);
lean_closure_set(v___f_2560_, 5, v_toBind_2558_);
lean_closure_set(v___f_2560_, 6, v_getEnv_2559_);
v___f_2561_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2561_, 0, v_inst_2553_);
lean_closure_set(v___f_2561_, 1, v_inst_2555_);
lean_closure_set(v___f_2561_, 2, v_toBind_2558_);
lean_closure_set(v___f_2561_, 3, v_getEnv_2559_);
lean_closure_set(v___f_2561_, 4, v___f_2560_);
v___x_2562_ = lean_apply_4(v_toBind_2558_, lean_box(0), lean_box(0), v_getEnv_2559_, v___f_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_inst_2567_, lean_object* v_docs_2568_, lean_object* v_deferred_2569_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2564_, v_inst_2565_, v_inst_2567_, v_docs_2568_, v_deferred_2569_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2571_, lean_object* v_inst_2572_, lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_docs_2576_, lean_object* v_deferred_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_addVersoModDocStringCore(v_m_2571_, v_inst_2572_, v_inst_2573_, v_inst_2574_, v_inst_2575_, v_docs_2576_, v_deferred_2577_);
lean_dec(v_inst_2574_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2579_, lean_object* v_as_2580_, size_t v_i_2581_, size_t v_stop_2582_, lean_object* v_b_2583_){
_start:
{
uint8_t v___x_2584_; 
v___x_2584_ = lean_usize_dec_eq(v_i_2581_, v_stop_2582_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v_index_2586_; lean_object* v_sourceString_2587_; lean_object* v_imports_2588_; lean_object* v_currNamespace_2589_; lean_object* v_openDecls_2590_; lean_object* v_options_2591_; lean_object* v_check_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2608_; 
v___x_2585_ = lean_array_uget(v_as_2580_, v_i_2581_);
v_index_2586_ = lean_ctor_get(v___x_2585_, 1);
v_sourceString_2587_ = lean_ctor_get(v___x_2585_, 2);
v_imports_2588_ = lean_ctor_get(v___x_2585_, 3);
v_currNamespace_2589_ = lean_ctor_get(v___x_2585_, 4);
v_openDecls_2590_ = lean_ctor_get(v___x_2585_, 5);
v_options_2591_ = lean_ctor_get(v___x_2585_, 6);
v_check_2592_ = lean_ctor_get(v___x_2585_, 7);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v___x_2585_, 0);
lean_dec(v_unused_2609_);
v___x_2594_ = v___x_2585_;
v_isShared_2595_ = v_isSharedCheck_2608_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_check_2592_);
lean_inc(v_options_2591_);
lean_inc(v_openDecls_2590_);
lean_inc(v_currNamespace_2589_);
lean_inc(v_imports_2588_);
lean_inc(v_sourceString_2587_);
lean_inc(v_index_2586_);
lean_dec(v___x_2585_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2608_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v_toEnvExtension_2597_; lean_object* v_asyncMode_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2596_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2597_ = lean_ctor_get(v___x_2596_, 0);
v_asyncMode_2598_ = lean_ctor_get(v_toEnvExtension_2597_, 2);
lean_inc(v_declName_2579_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_declName_2579_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2599_);
v___x_2601_ = v___x_2594_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_index_2586_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_sourceString_2587_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_imports_2588_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v_currNamespace_2589_);
lean_ctor_set(v_reuseFailAlloc_2607_, 5, v_openDecls_2590_);
lean_ctor_set(v_reuseFailAlloc_2607_, 6, v_options_2591_);
lean_ctor_set(v_reuseFailAlloc_2607_, 7, v_check_2592_);
v___x_2601_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; 
v___x_2602_ = lean_box(0);
v___x_2603_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2596_, v_b_2583_, v___x_2601_, v_asyncMode_2598_, v___x_2602_);
v___x_2604_ = ((size_t)1ULL);
v___x_2605_ = lean_usize_add(v_i_2581_, v___x_2604_);
v_i_2581_ = v___x_2605_;
v_b_2583_ = v___x_2603_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2579_);
return v_b_2583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2610_, lean_object* v_as_2611_, lean_object* v_i_2612_, lean_object* v_stop_2613_, lean_object* v_b_2614_){
_start:
{
size_t v_i_boxed_2615_; size_t v_stop_boxed_2616_; lean_object* v_res_2617_; 
v_i_boxed_2615_ = lean_unbox_usize(v_i_2612_);
lean_dec(v_i_2612_);
v_stop_boxed_2616_ = lean_unbox_usize(v_stop_2613_);
lean_dec(v_stop_2613_);
v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2610_, v_as_2611_, v_i_boxed_2615_, v_stop_boxed_2616_, v_b_2614_);
lean_dec_ref(v_as_2611_);
return v_res_2617_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2624_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
lean_ctor_set(v___x_2624_, 2, v___x_2623_);
lean_ctor_set(v___x_2624_, 3, v___x_2623_);
lean_ctor_set(v___x_2624_, 4, v___x_2623_);
lean_ctor_set(v___x_2624_, 5, v___x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2625_, lean_object* v_docs_2626_, lean_object* v_deferred_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2667_; lean_object* v___y_2668_; uint8_t v___x_2686_; 
v___x_2686_ = l_Lean_Name_isAnonymous(v_declName_2625_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v_env_2688_; lean_object* v___x_2689_; 
v___x_2687_ = lean_st_ref_get(v___y_2633_);
v_env_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc_ref(v_env_2688_);
lean_dec(v___x_2687_);
v___x_2689_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2688_, v_declName_2625_);
lean_dec_ref(v_env_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
v___y_2667_ = v___y_2631_;
v___y_2668_ = v___y_2633_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2704_; 
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v___x_2689_, 0);
lean_dec(v_unused_2705_);
v___x_2691_ = v___x_2689_;
v_isShared_2692_ = v_isSharedCheck_2704_;
goto v_resetjp_2690_;
}
else
{
lean_dec(v___x_2689_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2704_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
if (v___x_2686_ == 0)
{
lean_object* v___x_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec_ref(v_docs_2626_);
v___x_2693_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2694_ = 1;
v___x_2695_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2625_, v___x_2694_);
v___x_2696_ = lean_string_append(v___x_2693_, v___x_2695_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2698_ = lean_string_append(v___x_2696_, v___x_2697_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 3);
lean_ctor_set(v___x_2691_, 0, v___x_2698_);
v___x_2700_ = v___x_2691_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = l_Lean_MessageData_ofFormat(v___x_2700_);
v___x_2702_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2701_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2702_;
}
}
else
{
lean_del_object(v___x_2691_);
v___y_2667_ = v___y_2631_;
v___y_2668_ = v___y_2633_;
goto v___jp_2666_;
}
}
}
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec_ref(v_docs_2626_);
lean_dec(v_declName_2625_);
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
v___jp_2635_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_mctx_2650_; lean_object* v_zetaDeltaFVarIds_2651_; lean_object* v_postponed_2652_; lean_object* v_diag_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2664_; 
v___x_2646_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2647_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2647_, 0, v___y_2645_);
lean_ctor_set(v___x_2647_, 1, v___y_2644_);
lean_ctor_set(v___x_2647_, 2, v___y_2639_);
lean_ctor_set(v___x_2647_, 3, v___y_2643_);
lean_ctor_set(v___x_2647_, 4, v___y_2642_);
lean_ctor_set(v___x_2647_, 5, v___x_2646_);
lean_ctor_set(v___x_2647_, 6, v___y_2638_);
lean_ctor_set(v___x_2647_, 7, v___y_2641_);
lean_ctor_set(v___x_2647_, 8, v___y_2636_);
v___x_2648_ = lean_st_ref_put(v___y_2640_, v___x_2647_);
v___x_2649_ = lean_st_ref_take(v___y_2637_);
v_mctx_2650_ = lean_ctor_get(v___x_2649_, 0);
v_zetaDeltaFVarIds_2651_ = lean_ctor_get(v___x_2649_, 2);
v_postponed_2652_ = lean_ctor_get(v___x_2649_, 3);
v_diag_2653_ = lean_ctor_get(v___x_2649_, 4);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2649_, 1);
lean_dec(v_unused_2665_);
v___x_2655_ = v___x_2649_;
v_isShared_2656_ = v_isSharedCheck_2664_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_diag_2653_);
lean_inc(v_postponed_2652_);
lean_inc(v_zetaDeltaFVarIds_2651_);
lean_inc(v_mctx_2650_);
lean_dec(v___x_2649_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2664_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2657_);
v___x_2659_ = v___x_2655_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_mctx_2650_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_zetaDeltaFVarIds_2651_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_postponed_2652_);
lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_diag_2653_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_st_ref_put(v___y_2637_, v___x_2659_);
v___x_2661_ = lean_box(0);
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
return v___x_2662_;
}
}
}
v___jp_2666_:
{
lean_object* v___x_2669_; lean_object* v_env_2670_; lean_object* v_nextMacroScope_2671_; lean_object* v_ngen_2672_; lean_object* v_auxDeclNGen_2673_; lean_object* v_traceState_2674_; lean_object* v_messages_2675_; lean_object* v_infoState_2676_; lean_object* v_snapshotTasks_2677_; lean_object* v___x_2678_; lean_object* v_env_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2669_ = lean_st_ref_take(v___y_2668_);
v_env_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc_ref(v_env_2670_);
v_nextMacroScope_2671_ = lean_ctor_get(v___x_2669_, 1);
lean_inc(v_nextMacroScope_2671_);
v_ngen_2672_ = lean_ctor_get(v___x_2669_, 2);
lean_inc_ref(v_ngen_2672_);
v_auxDeclNGen_2673_ = lean_ctor_get(v___x_2669_, 3);
lean_inc_ref(v_auxDeclNGen_2673_);
v_traceState_2674_ = lean_ctor_get(v___x_2669_, 4);
lean_inc_ref(v_traceState_2674_);
v_messages_2675_ = lean_ctor_get(v___x_2669_, 6);
lean_inc_ref(v_messages_2675_);
v_infoState_2676_ = lean_ctor_get(v___x_2669_, 7);
lean_inc_ref(v_infoState_2676_);
v_snapshotTasks_2677_ = lean_ctor_get(v___x_2669_, 8);
lean_inc_ref(v_snapshotTasks_2677_);
lean_dec(v___x_2669_);
v___x_2678_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2625_);
v_env_2679_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2678_, v_env_2670_, v_declName_2625_, v_docs_2626_);
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = lean_array_get_size(v_deferred_2627_);
v___x_2682_ = lean_nat_dec_lt(v___x_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_dec(v_declName_2625_);
v___y_2636_ = v_snapshotTasks_2677_;
v___y_2637_ = v___y_2667_;
v___y_2638_ = v_messages_2675_;
v___y_2639_ = v_ngen_2672_;
v___y_2640_ = v___y_2668_;
v___y_2641_ = v_infoState_2676_;
v___y_2642_ = v_traceState_2674_;
v___y_2643_ = v_auxDeclNGen_2673_;
v___y_2644_ = v_nextMacroScope_2671_;
v___y_2645_ = v_env_2679_;
goto v___jp_2635_;
}
else
{
size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = ((size_t)0ULL);
v___x_2684_ = lean_usize_of_nat(v___x_2681_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2625_, v_deferred_2627_, v___x_2683_, v___x_2684_, v_env_2679_);
v___y_2636_ = v_snapshotTasks_2677_;
v___y_2637_ = v___y_2667_;
v___y_2638_ = v_messages_2675_;
v___y_2639_ = v_ngen_2672_;
v___y_2640_ = v___y_2668_;
v___y_2641_ = v_infoState_2676_;
v___y_2642_ = v_traceState_2674_;
v___y_2643_ = v_auxDeclNGen_2673_;
v___y_2644_ = v_nextMacroScope_2671_;
v___y_2645_ = v___x_2685_;
goto v___jp_2635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2708_, lean_object* v_docs_2709_, lean_object* v_deferred_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2708_, v_docs_2709_, v_deferred_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec_ref(v_deferred_2710_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2719_, lean_object* v_binders_2720_, lean_object* v_docComment_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___x_2749_; lean_object* v_env_2750_; lean_object* v___x_2751_; 
v___x_2749_ = lean_st_ref_get(v_a_2727_);
v_env_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc_ref(v_env_2750_);
lean_dec(v___x_2749_);
v___x_2751_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2750_, v_declName_2719_);
lean_dec_ref(v_env_2750_);
if (lean_obj_tag(v___x_2751_) == 0)
{
v___y_2730_ = v_a_2722_;
v___y_2731_ = v_a_2723_;
v___y_2732_ = v_a_2724_;
v___y_2733_ = v_a_2725_;
v___y_2734_ = v_a_2726_;
v___y_2735_ = v_a_2727_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_binders_2720_);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v___x_2751_, 0);
lean_dec(v_unused_2767_);
v___x_2753_ = v___x_2751_;
v_isShared_2754_ = v_isSharedCheck_2766_;
goto v_resetjp_2752_;
}
else
{
lean_dec(v___x_2751_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2766_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; uint8_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2755_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2756_ = 1;
v___x_2757_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2719_, v___x_2756_);
v___x_2758_ = lean_string_append(v___x_2755_, v___x_2757_);
lean_dec_ref(v___x_2757_);
v___x_2759_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2760_ = lean_string_append(v___x_2758_, v___x_2759_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 3);
lean_ctor_set(v___x_2753_, 0, v___x_2760_);
v___x_2762_ = v___x_2753_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = l_Lean_MessageData_ofFormat(v___x_2762_);
v___x_2764_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2763_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
return v___x_2764_;
}
}
}
v___jp_2729_:
{
lean_object* v___x_2736_; 
lean_inc(v_declName_2719_);
v___x_2736_ = l_Lean_versoDocString(v_declName_2719_, v_binders_2720_, v_docComment_2721_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v_toVersoDocString_2738_; lean_object* v_deferredChecks_2739_; lean_object* v___x_2740_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v_toVersoDocString_2738_ = lean_ctor_get(v_a_2737_, 0);
lean_inc_ref(v_toVersoDocString_2738_);
v_deferredChecks_2739_ = lean_ctor_get(v_a_2737_, 1);
lean_inc_ref(v_deferredChecks_2739_);
lean_dec(v_a_2737_);
v___x_2740_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2719_, v_toVersoDocString_2738_, v_deferredChecks_2739_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec_ref(v_deferredChecks_2739_);
return v___x_2740_;
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_declName_2719_);
v_a_2741_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2736_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2736_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2768_, lean_object* v_binders_2769_, lean_object* v_docComment_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_addVersoDocString(v_declName_2768_, v_binders_2769_, v_docComment_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_docComment_2770_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2779_, lean_object* v_docComment_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___x_2808_; lean_object* v_env_2809_; lean_object* v___x_2810_; 
v___x_2808_ = lean_st_ref_get(v_a_2786_);
v_env_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2809_);
lean_dec(v___x_2808_);
v___x_2810_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2809_, v_declName_2779_);
lean_dec_ref(v_env_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
v___y_2789_ = v_a_2781_;
v___y_2790_ = v_a_2782_;
v___y_2791_ = v_a_2783_;
v___y_2792_ = v_a_2784_;
v___y_2793_ = v_a_2785_;
v___y_2794_ = v_a_2786_;
goto v___jp_2788_;
}
else
{
lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref(v_docComment_2780_);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2810_, 0);
lean_dec(v_unused_2826_);
v___x_2812_ = v___x_2810_;
v_isShared_2813_ = v_isSharedCheck_2825_;
goto v_resetjp_2811_;
}
else
{
lean_dec(v___x_2810_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2825_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2814_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2815_ = 1;
v___x_2816_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2779_, v___x_2815_);
v___x_2817_ = lean_string_append(v___x_2814_, v___x_2816_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2819_ = lean_string_append(v___x_2817_, v___x_2818_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 3);
lean_ctor_set(v___x_2812_, 0, v___x_2819_);
v___x_2821_ = v___x_2812_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = l_Lean_MessageData_ofFormat(v___x_2821_);
v___x_2823_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2822_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
return v___x_2823_;
}
}
}
v___jp_2788_:
{
lean_object* v___x_2795_; 
lean_inc(v_declName_2779_);
v___x_2795_ = l_Lean_versoDocStringFromString(v_declName_2779_, v_docComment_2780_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v_toVersoDocString_2797_; lean_object* v_deferredChecks_2798_; lean_object* v___x_2799_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v_toVersoDocString_2797_ = lean_ctor_get(v_a_2796_, 0);
lean_inc_ref(v_toVersoDocString_2797_);
v_deferredChecks_2798_ = lean_ctor_get(v_a_2796_, 1);
lean_inc_ref(v_deferredChecks_2798_);
lean_dec(v_a_2796_);
v___x_2799_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2779_, v_toVersoDocString_2797_, v_deferredChecks_2798_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec_ref(v_deferredChecks_2798_);
return v___x_2799_;
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_declName_2779_);
v_a_2800_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2795_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2795_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2827_, lean_object* v_docComment_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_addVersoDocStringFromString(v_declName_2827_, v_docComment_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2837_, lean_object* v_msgData_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
uint8_t v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = 2;
v___x_2845_ = 0;
v___x_2846_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2837_, v_msgData_2838_, v___x_2844_, v___x_2845_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2847_, lean_object* v_msgData_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2847_, v_msgData_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v_ref_2847_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2855_, lean_object* v_str_2856_, lean_object* v_as_2857_, size_t v_sz_2858_, size_t v_i_2859_, lean_object* v_b_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_a_2869_; uint8_t v___x_2873_; 
v___x_2873_ = lean_usize_dec_lt(v_i_2859_, v_sz_2858_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_b_2860_);
return v___x_2874_;
}
else
{
lean_object* v_a_2875_; lean_object* v_fst_2876_; lean_object* v_snd_2877_; lean_object* v_start_2878_; lean_object* v_stop_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2899_; 
v_a_2875_ = lean_array_uget_borrowed(v_as_2857_, v_i_2859_);
v_fst_2876_ = lean_ctor_get(v_a_2875_, 0);
lean_inc(v_fst_2876_);
v_snd_2877_ = lean_ctor_get(v_a_2875_, 1);
v_start_2878_ = lean_ctor_get(v_fst_2876_, 0);
v_stop_2879_ = lean_ctor_get(v_fst_2876_, 1);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_fst_2876_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2881_ = v_fst_2876_;
v_isShared_2882_ = v_isSharedCheck_2899_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_stop_2879_);
lean_inc(v_start_2878_);
lean_dec(v_fst_2876_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2899_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_box(0);
if (lean_obj_tag(v___y_2855_) == 1)
{
lean_object* v_val_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2891_; 
v_val_2884_ = lean_ctor_get(v___y_2855_, 0);
v___x_2885_ = lean_nat_add(v_val_2884_, v_start_2878_);
v___x_2886_ = lean_nat_add(v_val_2884_, v_stop_2879_);
v___x_2887_ = 0;
v___x_2888_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2888_, 0, v___x_2885_);
lean_ctor_set(v___x_2888_, 1, v___x_2886_);
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*2, v___x_2887_);
v___x_2889_ = lean_string_utf8_extract(v_str_2856_, v_start_2878_, v_stop_2879_);
lean_dec(v_stop_2879_);
lean_dec(v_start_2878_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 2);
lean_ctor_set(v___x_2881_, 1, v___x_2889_);
lean_ctor_set(v___x_2881_, 0, v___x_2888_);
v___x_2891_ = v___x_2881_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_inc(v_snd_2877_);
v___x_2892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_snd_2877_);
v___x_2893_ = l_Lean_MessageData_ofFormat(v___x_2892_);
v___x_2894_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2891_, v___x_2893_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec_ref(v___x_2891_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_dec_ref_known(v___x_2894_, 1);
v_a_2869_ = v___x_2883_;
goto v___jp_2868_;
}
else
{
return v___x_2894_;
}
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_del_object(v___x_2881_);
lean_dec(v_stop_2879_);
lean_dec(v_start_2878_);
lean_inc(v_snd_2877_);
v___x_2896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2896_, 0, v_snd_2877_);
v___x_2897_ = l_Lean_MessageData_ofFormat(v___x_2896_);
v___x_2898_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_2897_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_dec_ref_known(v___x_2898_, 1);
v_a_2869_ = v___x_2883_;
goto v___jp_2868_;
}
else
{
return v___x_2898_;
}
}
}
}
v___jp_2868_:
{
size_t v___x_2870_; size_t v___x_2871_; 
v___x_2870_ = ((size_t)1ULL);
v___x_2871_ = lean_usize_add(v_i_2859_, v___x_2870_);
v_i_2859_ = v___x_2871_;
v_b_2860_ = v_a_2869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2900_, lean_object* v_str_2901_, lean_object* v_as_2902_, lean_object* v_sz_2903_, lean_object* v_i_2904_, lean_object* v_b_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
size_t v_sz_boxed_2913_; size_t v_i_boxed_2914_; lean_object* v_res_2915_; 
v_sz_boxed_2913_ = lean_unbox_usize(v_sz_2903_);
lean_dec(v_sz_2903_);
v_i_boxed_2914_ = lean_unbox_usize(v_i_2904_);
lean_dec(v_i_2904_);
v_res_2915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2900_, v_str_2901_, v_as_2902_, v_sz_boxed_2913_, v_i_boxed_2914_, v_b_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec_ref(v_as_2902_);
lean_dec_ref(v_str_2901_);
lean_dec(v___y_2900_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_str_2924_; lean_object* v___y_2926_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_str_2924_ = l_Lean_TSyntax_getDocString(v_docstring_2916_);
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = l_Lean_Syntax_getArg(v_docstring_2916_, v___x_2941_);
v___x_2943_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2942_);
lean_dec(v___x_2942_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_box(0);
v___y_2926_ = v___x_2944_;
goto v___jp_2925_;
}
else
{
lean_object* v_val_2945_; uint8_t v___x_2946_; lean_object* v___x_2947_; 
v_val_2945_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_val_2945_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2946_ = 0;
v___x_2947_ = l_Lean_SourceInfo_getPos_x3f(v_val_2945_, v___x_2946_);
lean_dec(v_val_2945_);
v___y_2926_ = v___x_2947_;
goto v___jp_2925_;
}
v___jp_2925_:
{
lean_object* v___x_2927_; lean_object* v_fst_2928_; lean_object* v___x_2929_; size_t v_sz_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
lean_inc_ref(v_str_2924_);
v___x_2927_ = l_Lean_rewriteManualLinksCore(v_str_2924_);
v_fst_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_fst_2928_);
lean_dec_ref(v___x_2927_);
v___x_2929_ = lean_box(0);
v_sz_2930_ = lean_array_size(v_fst_2928_);
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2926_, v_str_2924_, v_fst_2928_, v_sz_2930_, v___x_2931_, v___x_2929_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v_fst_2928_);
lean_dec_ref(v_str_2924_);
lean_dec(v___y_2926_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; 
v_unused_2940_ = lean_ctor_get(v___x_2932_, 0);
lean_dec(v_unused_2940_);
v___x_2934_ = v___x_2932_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_dec(v___x_2932_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2929_);
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2929_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
else
{
return v___x_2932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v_docstring_2948_);
return v_res_2956_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2959_ = l_Lean_stringToMessageData(v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_val_2975_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_unsigned_to_nat(1u);
v___x_2983_ = l_Lean_Syntax_getArg(v_stx_2960_, v___x_2982_);
switch(lean_obj_tag(v___x_2983_))
{
case 2:
{
lean_object* v_val_2984_; 
lean_dec(v_stx_2960_);
v_val_2984_ = lean_ctor_get(v___x_2983_, 1);
lean_inc_ref(v_val_2984_);
lean_dec_ref_known(v___x_2983_, 2);
v_val_2975_ = v_val_2984_;
goto v___jp_2974_;
}
case 1:
{
lean_object* v_kind_2985_; 
v_kind_2985_ = lean_ctor_get(v___x_2983_, 1);
lean_inc(v_kind_2985_);
if (lean_obj_tag(v_kind_2985_) == 1)
{
lean_object* v_pre_2986_; 
v_pre_2986_ = lean_ctor_get(v_kind_2985_, 0);
lean_inc(v_pre_2986_);
if (lean_obj_tag(v_pre_2986_) == 1)
{
lean_object* v_pre_2987_; 
v_pre_2987_ = lean_ctor_get(v_pre_2986_, 0);
lean_inc(v_pre_2987_);
if (lean_obj_tag(v_pre_2987_) == 1)
{
lean_object* v_pre_2988_; 
v_pre_2988_ = lean_ctor_get(v_pre_2987_, 0);
lean_inc(v_pre_2988_);
if (lean_obj_tag(v_pre_2988_) == 1)
{
lean_object* v_pre_2989_; 
v_pre_2989_ = lean_ctor_get(v_pre_2988_, 0);
if (lean_obj_tag(v_pre_2989_) == 0)
{
lean_object* v_str_2990_; lean_object* v_str_2991_; lean_object* v_str_2992_; lean_object* v_str_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v_str_2990_ = lean_ctor_get(v_kind_2985_, 1);
lean_inc_ref(v_str_2990_);
lean_dec_ref_known(v_kind_2985_, 2);
v_str_2991_ = lean_ctor_get(v_pre_2986_, 1);
lean_inc_ref(v_str_2991_);
lean_dec_ref_known(v_pre_2986_, 2);
v_str_2992_ = lean_ctor_get(v_pre_2987_, 1);
lean_inc_ref(v_str_2992_);
lean_dec_ref_known(v_pre_2987_, 2);
v_str_2993_ = lean_ctor_get(v_pre_2988_, 1);
lean_inc_ref(v_str_2993_);
lean_dec_ref_known(v_pre_2988_, 2);
v___x_2994_ = ((lean_object*)(l_Lean_VersoDocstringView_of___closed__0));
v___x_2995_ = lean_string_dec_eq(v_str_2993_, v___x_2994_);
lean_dec_ref(v_str_2993_);
if (v___x_2995_ == 0)
{
lean_dec_ref(v_str_2992_);
lean_dec_ref(v_str_2991_);
lean_dec_ref(v_str_2990_);
lean_dec_ref_known(v___x_2983_, 3);
goto v___jp_2968_;
}
else
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_2997_ = lean_string_dec_eq(v_str_2992_, v___x_2996_);
lean_dec_ref(v_str_2992_);
if (v___x_2997_ == 0)
{
lean_dec_ref(v_str_2991_);
lean_dec_ref(v_str_2990_);
lean_dec_ref_known(v___x_2983_, 3);
goto v___jp_2968_;
}
else
{
lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_2999_ = lean_string_dec_eq(v_str_2991_, v___x_2998_);
lean_dec_ref(v_str_2991_);
if (v___x_2999_ == 0)
{
lean_dec_ref(v_str_2990_);
lean_dec_ref_known(v___x_2983_, 3);
goto v___jp_2968_;
}
else
{
lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_3001_ = lean_string_dec_eq(v_str_2990_, v___x_3000_);
lean_dec_ref(v_str_2990_);
if (v___x_3001_ == 0)
{
lean_dec_ref_known(v___x_2983_, 3);
goto v___jp_2968_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_unsigned_to_nat(0u);
v___x_3003_ = l_Lean_Syntax_getArg(v___x_2983_, v___x_3002_);
lean_dec_ref_known(v___x_2983_, 3);
if (lean_obj_tag(v___x_3003_) == 2)
{
lean_object* v_val_3004_; 
lean_dec(v_stx_2960_);
v_val_3004_ = lean_ctor_get(v___x_3003_, 1);
lean_inc_ref(v_val_3004_);
lean_dec_ref_known(v___x_3003_, 2);
v_val_2975_ = v_val_3004_;
goto v___jp_2974_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec(v___x_3003_);
v___x_3005_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2960_);
v___x_3006_ = l_Lean_MessageData_ofSyntax(v_stx_2960_);
v___x_3007_ = l_Lean_indentD(v___x_3006_);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3005_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2960_, v___x_3008_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v_stx_2960_);
return v___x_3009_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2988_, 2);
lean_dec_ref_known(v_pre_2987_, 2);
lean_dec_ref_known(v_pre_2986_, 2);
lean_dec_ref_known(v_kind_2985_, 2);
lean_dec_ref_known(v___x_2983_, 3);
goto v___jp_2968_;
}
}
else
{
lean_dec(v_pre_2988_);
lean_dec_ref_known(v_pre_2987_, 2);
lean_dec_ref_known(v_pre_2986_, 2);
lean_dec_ref_known(v_kind_2985_, 2);
lean_dec_ref_known(v___x_2983_, 3);
goto v___jp_2968_;
}
}
else
{
lean_dec(v_pre_2987_);
lean_dec_ref_known(v_pre_2986_, 2);
lean_dec_ref_known(v_kind_2985_, 2);
lean_dec_ref_known(v___x_2983_, 3);
goto v___jp_2968_;
}
}
else
{
lean_dec(v_pre_2986_);
lean_dec_ref_known(v_kind_2985_, 2);
lean_dec_ref_known(v___x_2983_, 3);
goto v___jp_2968_;
}
}
else
{
lean_dec_ref_known(v___x_2983_, 3);
lean_dec(v_kind_2985_);
goto v___jp_2968_;
}
}
default: 
{
lean_dec(v___x_2983_);
goto v___jp_2968_;
}
}
v___jp_2968_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2969_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2960_);
v___x_2970_ = l_Lean_MessageData_ofSyntax(v_stx_2960_);
v___x_2971_ = l_Lean_indentD(v___x_2970_);
v___x_2972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2969_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2960_, v___x_2972_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v_stx_2960_);
return v___x_2973_;
}
v___jp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2976_ = lean_unsigned_to_nat(0u);
v___x_2977_ = lean_string_utf8_byte_size(v_val_2975_);
v___x_2978_ = lean_unsigned_to_nat(2u);
v___x_2979_ = lean_nat_sub(v___x_2977_, v___x_2978_);
v___x_2980_ = lean_string_utf8_extract(v_val_2975_, v___x_2976_, v___x_2979_);
lean_dec(v___x_2979_);
lean_dec_ref(v_val_2975_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_3019_, lean_object* v_docComment_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; uint8_t v___x_3091_; 
v___x_3091_ = l_Lean_Name_isAnonymous(v_declName_3019_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v_env_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_st_ref_get(v___y_3026_);
v_env_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc_ref(v_env_3093_);
lean_dec(v___x_3092_);
v___x_3094_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3093_, v_declName_3019_);
lean_dec_ref(v_env_3093_);
if (lean_obj_tag(v___x_3094_) == 0)
{
v___y_3029_ = v___y_3021_;
v___y_3030_ = v___y_3022_;
v___y_3031_ = v___y_3023_;
v___y_3032_ = v___y_3024_;
v___y_3033_ = v___y_3025_;
v___y_3034_ = v___y_3026_;
goto v___jp_3028_;
}
else
{
lean_dec_ref_known(v___x_3094_, 1);
if (v___x_3091_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_dec(v_docComment_3020_);
v___x_3095_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3096_ = l_Lean_MessageData_ofConstName(v_declName_3019_, v___x_3091_);
v___x_3097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3099_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v___x_3100_;
}
else
{
v___y_3029_ = v___y_3021_;
v___y_3030_ = v___y_3022_;
v___y_3031_ = v___y_3023_;
v___y_3032_ = v___y_3024_;
v___y_3033_ = v___y_3025_;
v___y_3034_ = v___y_3026_;
goto v___jp_3028_;
}
}
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_dec(v_docComment_3020_);
lean_dec(v_declName_3019_);
v___x_3101_ = lean_box(0);
v___x_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
return v___x_3102_;
}
v___jp_3028_:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_3020_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v___x_3036_; 
lean_dec_ref_known(v___x_3035_, 1);
v___x_3036_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_3020_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3082_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3082_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3082_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v_env_3042_; lean_object* v_nextMacroScope_3043_; lean_object* v_ngen_3044_; lean_object* v_auxDeclNGen_3045_; lean_object* v_traceState_3046_; lean_object* v_messages_3047_; lean_object* v_infoState_3048_; lean_object* v_snapshotTasks_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3080_; 
v___x_3041_ = lean_st_ref_take(v___y_3034_);
v_env_3042_ = lean_ctor_get(v___x_3041_, 0);
v_nextMacroScope_3043_ = lean_ctor_get(v___x_3041_, 1);
v_ngen_3044_ = lean_ctor_get(v___x_3041_, 2);
v_auxDeclNGen_3045_ = lean_ctor_get(v___x_3041_, 3);
v_traceState_3046_ = lean_ctor_get(v___x_3041_, 4);
v_messages_3047_ = lean_ctor_get(v___x_3041_, 6);
v_infoState_3048_ = lean_ctor_get(v___x_3041_, 7);
v_snapshotTasks_3049_ = lean_ctor_get(v___x_3041_, 8);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; 
v_unused_3081_ = lean_ctor_get(v___x_3041_, 5);
lean_dec(v_unused_3081_);
v___x_3051_ = v___x_3041_;
v_isShared_3052_ = v_isSharedCheck_3080_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_snapshotTasks_3049_);
lean_inc(v_infoState_3048_);
lean_inc(v_messages_3047_);
lean_inc(v_traceState_3046_);
lean_inc(v_auxDeclNGen_3045_);
lean_inc(v_ngen_3044_);
lean_inc(v_nextMacroScope_3043_);
lean_inc(v_env_3042_);
lean_dec(v___x_3041_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3080_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3053_ = l_Lean_docStringExt;
v___x_3054_ = l_String_removeLeadingSpaces(v_a_3037_);
v___x_3055_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3053_, v_env_3042_, v_declName_3019_, v___x_3054_);
v___x_3056_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 5, v___x_3056_);
lean_ctor_set(v___x_3051_, 0, v___x_3055_);
v___x_3058_ = v___x_3051_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_nextMacroScope_3043_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_ngen_3044_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_auxDeclNGen_3045_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_traceState_3046_);
lean_ctor_set(v_reuseFailAlloc_3079_, 5, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3079_, 6, v_messages_3047_);
lean_ctor_set(v_reuseFailAlloc_3079_, 7, v_infoState_3048_);
lean_ctor_set(v_reuseFailAlloc_3079_, 8, v_snapshotTasks_3049_);
v___x_3058_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_mctx_3061_; lean_object* v_zetaDeltaFVarIds_3062_; lean_object* v_postponed_3063_; lean_object* v_diag_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3077_; 
v___x_3059_ = lean_st_ref_put(v___y_3034_, v___x_3058_);
v___x_3060_ = lean_st_ref_take(v___y_3032_);
v_mctx_3061_ = lean_ctor_get(v___x_3060_, 0);
v_zetaDeltaFVarIds_3062_ = lean_ctor_get(v___x_3060_, 2);
v_postponed_3063_ = lean_ctor_get(v___x_3060_, 3);
v_diag_3064_ = lean_ctor_get(v___x_3060_, 4);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3060_, 1);
lean_dec(v_unused_3078_);
v___x_3066_ = v___x_3060_;
v_isShared_3067_ = v_isSharedCheck_3077_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_diag_3064_);
lean_inc(v_postponed_3063_);
lean_inc(v_zetaDeltaFVarIds_3062_);
lean_inc(v_mctx_3061_);
lean_dec(v___x_3060_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3077_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3068_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v___x_3068_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_mctx_3061_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___x_3068_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_zetaDeltaFVarIds_3062_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_postponed_3063_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v_diag_3064_);
v___x_3070_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3071_ = lean_st_ref_put(v___y_3032_, v___x_3070_);
v___x_3072_ = lean_box(0);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3072_);
v___x_3074_ = v___x_3039_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_declName_3019_);
v_a_3083_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3036_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3036_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_dec(v_docComment_3020_);
lean_dec(v_declName_3019_);
return v___x_3035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3103_, lean_object* v_docComment_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3103_, v_docComment_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3113_, lean_object* v_declName_3114_, lean_object* v_binders_3115_, lean_object* v_docComment_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_){
_start:
{
if (v_isVerso_3113_ == 0)
{
lean_object* v___x_3124_; 
lean_dec(v_binders_3115_);
v___x_3124_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3114_, v_docComment_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_addVersoDocString(v_declName_3114_, v_binders_3115_, v_docComment_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
lean_dec(v_docComment_3116_);
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3126_, lean_object* v_declName_3127_, lean_object* v_binders_3128_, lean_object* v_docComment_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
uint8_t v_isVerso_boxed_3137_; lean_object* v_res_3138_; 
v_isVerso_boxed_3137_ = lean_unbox(v_isVerso_3126_);
v_res_3138_ = l_Lean_addDocStringOf(v_isVerso_boxed_3137_, v_declName_3127_, v_binders_3128_, v_docComment_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3139_, lean_object* v_msgData_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3139_, v_msgData_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3149_, lean_object* v_msgData_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3149_, v_msgData_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v_ref_3149_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3159_, lean_object* v_t_3160_){
_start:
{
if (lean_obj_tag(v_t_3160_) == 0)
{
lean_object* v_k_3161_; lean_object* v_v_3162_; lean_object* v_l_3163_; lean_object* v_r_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3818_; 
v_k_3161_ = lean_ctor_get(v_t_3160_, 1);
v_v_3162_ = lean_ctor_get(v_t_3160_, 2);
v_l_3163_ = lean_ctor_get(v_t_3160_, 3);
v_r_3164_ = lean_ctor_get(v_t_3160_, 4);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_t_3160_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v_t_3160_, 0);
lean_dec(v_unused_3819_);
v___x_3166_ = v_t_3160_;
v_isShared_3167_ = v_isSharedCheck_3818_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_r_3164_);
lean_inc(v_l_3163_);
lean_inc(v_v_3162_);
lean_inc(v_k_3161_);
lean_dec(v_t_3160_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3818_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
uint8_t v___x_3168_; 
v___x_3168_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3159_, v_k_3161_);
switch(v___x_3168_)
{
case 0:
{
lean_object* v_impl_3169_; lean_object* v___x_3170_; 
v_impl_3169_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3159_, v_l_3163_);
v___x_3170_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3169_) == 0)
{
if (lean_obj_tag(v_r_3164_) == 0)
{
lean_object* v_size_3171_; lean_object* v_size_3172_; lean_object* v_k_3173_; lean_object* v_v_3174_; lean_object* v_l_3175_; lean_object* v_r_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v_size_3171_ = lean_ctor_get(v_impl_3169_, 0);
lean_inc(v_size_3171_);
v_size_3172_ = lean_ctor_get(v_r_3164_, 0);
v_k_3173_ = lean_ctor_get(v_r_3164_, 1);
v_v_3174_ = lean_ctor_get(v_r_3164_, 2);
v_l_3175_ = lean_ctor_get(v_r_3164_, 3);
lean_inc(v_l_3175_);
v_r_3176_ = lean_ctor_get(v_r_3164_, 4);
v___x_3177_ = lean_unsigned_to_nat(3u);
v___x_3178_ = lean_nat_mul(v___x_3177_, v_size_3171_);
v___x_3179_ = lean_nat_dec_lt(v___x_3178_, v_size_3172_);
lean_dec(v___x_3178_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3183_; 
lean_dec(v_l_3175_);
v___x_3180_ = lean_nat_add(v___x_3170_, v_size_3171_);
lean_dec(v_size_3171_);
v___x_3181_ = lean_nat_add(v___x_3180_, v_size_3172_);
lean_dec(v___x_3180_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 3, v_impl_3169_);
lean_ctor_set(v___x_3166_, 0, v___x_3181_);
v___x_3183_ = v___x_3166_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_impl_3169_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_r_3164_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
else
{
lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3248_; 
lean_inc(v_r_3176_);
lean_inc(v_v_3174_);
lean_inc(v_k_3173_);
lean_inc(v_size_3172_);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; lean_object* v_unused_3250_; lean_object* v_unused_3251_; lean_object* v_unused_3252_; lean_object* v_unused_3253_; 
v_unused_3249_ = lean_ctor_get(v_r_3164_, 4);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_r_3164_, 3);
lean_dec(v_unused_3250_);
v_unused_3251_ = lean_ctor_get(v_r_3164_, 2);
lean_dec(v_unused_3251_);
v_unused_3252_ = lean_ctor_get(v_r_3164_, 1);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v_r_3164_, 0);
lean_dec(v_unused_3253_);
v___x_3186_ = v_r_3164_;
v_isShared_3187_ = v_isSharedCheck_3248_;
goto v_resetjp_3185_;
}
else
{
lean_dec(v_r_3164_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3248_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_size_3188_; lean_object* v_k_3189_; lean_object* v_v_3190_; lean_object* v_l_3191_; lean_object* v_r_3192_; lean_object* v_size_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; uint8_t v___x_3196_; 
v_size_3188_ = lean_ctor_get(v_l_3175_, 0);
v_k_3189_ = lean_ctor_get(v_l_3175_, 1);
v_v_3190_ = lean_ctor_get(v_l_3175_, 2);
v_l_3191_ = lean_ctor_get(v_l_3175_, 3);
v_r_3192_ = lean_ctor_get(v_l_3175_, 4);
v_size_3193_ = lean_ctor_get(v_r_3176_, 0);
v___x_3194_ = lean_unsigned_to_nat(2u);
v___x_3195_ = lean_nat_mul(v___x_3194_, v_size_3193_);
v___x_3196_ = lean_nat_dec_lt(v_size_3188_, v___x_3195_);
lean_dec(v___x_3195_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3224_; 
lean_inc(v_r_3192_);
lean_inc(v_l_3191_);
lean_inc(v_v_3190_);
lean_inc(v_k_3189_);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_l_3175_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; lean_object* v_unused_3226_; lean_object* v_unused_3227_; lean_object* v_unused_3228_; lean_object* v_unused_3229_; 
v_unused_3225_ = lean_ctor_get(v_l_3175_, 4);
lean_dec(v_unused_3225_);
v_unused_3226_ = lean_ctor_get(v_l_3175_, 3);
lean_dec(v_unused_3226_);
v_unused_3227_ = lean_ctor_get(v_l_3175_, 2);
lean_dec(v_unused_3227_);
v_unused_3228_ = lean_ctor_get(v_l_3175_, 1);
lean_dec(v_unused_3228_);
v_unused_3229_ = lean_ctor_get(v_l_3175_, 0);
lean_dec(v_unused_3229_);
v___x_3198_ = v_l_3175_;
v_isShared_3199_ = v_isSharedCheck_3224_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v_l_3175_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3224_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3214_; 
v___x_3200_ = lean_nat_add(v___x_3170_, v_size_3171_);
lean_dec(v_size_3171_);
v___x_3201_ = lean_nat_add(v___x_3200_, v_size_3172_);
lean_dec(v_size_3172_);
if (lean_obj_tag(v_l_3191_) == 0)
{
lean_object* v_size_3222_; 
v_size_3222_ = lean_ctor_get(v_l_3191_, 0);
lean_inc(v_size_3222_);
v___y_3214_ = v_size_3222_;
goto v___jp_3213_;
}
else
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_unsigned_to_nat(0u);
v___y_3214_ = v___x_3223_;
goto v___jp_3213_;
}
v___jp_3202_:
{
lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3206_ = lean_nat_add(v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec(v___y_3204_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v_r_3176_);
lean_ctor_set(v___x_3198_, 3, v_r_3192_);
lean_ctor_set(v___x_3198_, 2, v_v_3174_);
lean_ctor_set(v___x_3198_, 1, v_k_3173_);
lean_ctor_set(v___x_3198_, 0, v___x_3206_);
v___x_3208_ = v___x_3198_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_k_3173_);
lean_ctor_set(v_reuseFailAlloc_3212_, 2, v_v_3174_);
lean_ctor_set(v_reuseFailAlloc_3212_, 3, v_r_3192_);
lean_ctor_set(v_reuseFailAlloc_3212_, 4, v_r_3176_);
v___x_3208_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3210_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 4, v___x_3208_);
lean_ctor_set(v___x_3186_, 3, v___y_3203_);
lean_ctor_set(v___x_3186_, 2, v_v_3190_);
lean_ctor_set(v___x_3186_, 1, v_k_3189_);
lean_ctor_set(v___x_3186_, 0, v___x_3201_);
v___x_3210_ = v___x_3186_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_k_3189_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_v_3190_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v___y_3203_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
v___jp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3215_ = lean_nat_add(v___x_3200_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec(v___x_3200_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_l_3191_);
lean_ctor_set(v___x_3166_, 3, v_impl_3169_);
lean_ctor_set(v___x_3166_, 0, v___x_3215_);
v___x_3217_ = v___x_3166_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3221_, 3, v_impl_3169_);
lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_l_3191_);
v___x_3217_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_nat_add(v___x_3170_, v_size_3193_);
if (lean_obj_tag(v_r_3192_) == 0)
{
lean_object* v_size_3219_; 
v_size_3219_ = lean_ctor_get(v_r_3192_, 0);
lean_inc(v_size_3219_);
v___y_3203_ = v___x_3217_;
v___y_3204_ = v___x_3218_;
v___y_3205_ = v_size_3219_;
goto v___jp_3202_;
}
else
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_unsigned_to_nat(0u);
v___y_3203_ = v___x_3217_;
v___y_3204_ = v___x_3218_;
v___y_3205_ = v___x_3220_;
goto v___jp_3202_;
}
}
}
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
lean_del_object(v___x_3166_);
v___x_3230_ = lean_nat_add(v___x_3170_, v_size_3171_);
lean_dec(v_size_3171_);
v___x_3231_ = lean_nat_add(v___x_3230_, v_size_3172_);
lean_dec(v_size_3172_);
v___x_3232_ = lean_nat_add(v___x_3230_, v_size_3188_);
lean_dec(v___x_3230_);
lean_inc_ref(v_impl_3169_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 4, v_l_3175_);
lean_ctor_set(v___x_3186_, 3, v_impl_3169_);
lean_ctor_set(v___x_3186_, 2, v_v_3162_);
lean_ctor_set(v___x_3186_, 1, v_k_3161_);
lean_ctor_set(v___x_3186_, 0, v___x_3232_);
v___x_3234_ = v___x_3186_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_impl_3169_);
lean_ctor_set(v_reuseFailAlloc_3247_, 4, v_l_3175_);
v___x_3234_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
v_isSharedCheck_3241_ = !lean_is_exclusive(v_impl_3169_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; lean_object* v_unused_3243_; lean_object* v_unused_3244_; lean_object* v_unused_3245_; lean_object* v_unused_3246_; 
v_unused_3242_ = lean_ctor_get(v_impl_3169_, 4);
lean_dec(v_unused_3242_);
v_unused_3243_ = lean_ctor_get(v_impl_3169_, 3);
lean_dec(v_unused_3243_);
v_unused_3244_ = lean_ctor_get(v_impl_3169_, 2);
lean_dec(v_unused_3244_);
v_unused_3245_ = lean_ctor_get(v_impl_3169_, 1);
lean_dec(v_unused_3245_);
v_unused_3246_ = lean_ctor_get(v_impl_3169_, 0);
lean_dec(v_unused_3246_);
v___x_3236_ = v_impl_3169_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_dec(v_impl_3169_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 4, v_r_3176_);
lean_ctor_set(v___x_3236_, 3, v___x_3234_);
lean_ctor_set(v___x_3236_, 2, v_v_3174_);
lean_ctor_set(v___x_3236_, 1, v_k_3173_);
lean_ctor_set(v___x_3236_, 0, v___x_3231_);
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_k_3173_);
lean_ctor_set(v_reuseFailAlloc_3240_, 2, v_v_3174_);
lean_ctor_set(v_reuseFailAlloc_3240_, 3, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3240_, 4, v_r_3176_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v_size_3254_ = lean_ctor_get(v_impl_3169_, 0);
lean_inc(v_size_3254_);
v___x_3255_ = lean_nat_add(v___x_3170_, v_size_3254_);
lean_dec(v_size_3254_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 3, v_impl_3169_);
lean_ctor_set(v___x_3166_, 0, v___x_3255_);
v___x_3257_ = v___x_3166_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3258_, 3, v_impl_3169_);
lean_ctor_set(v_reuseFailAlloc_3258_, 4, v_r_3164_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
else
{
if (lean_obj_tag(v_r_3164_) == 0)
{
lean_object* v_l_3259_; 
v_l_3259_ = lean_ctor_get(v_r_3164_, 3);
lean_inc(v_l_3259_);
if (lean_obj_tag(v_l_3259_) == 0)
{
lean_object* v_r_3260_; 
v_r_3260_ = lean_ctor_get(v_r_3164_, 4);
lean_inc(v_r_3260_);
if (lean_obj_tag(v_r_3260_) == 0)
{
lean_object* v_size_3261_; lean_object* v_k_3262_; lean_object* v_v_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3276_; 
v_size_3261_ = lean_ctor_get(v_r_3164_, 0);
v_k_3262_ = lean_ctor_get(v_r_3164_, 1);
v_v_3263_ = lean_ctor_get(v_r_3164_, 2);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; lean_object* v_unused_3278_; 
v_unused_3277_ = lean_ctor_get(v_r_3164_, 4);
lean_dec(v_unused_3277_);
v_unused_3278_ = lean_ctor_get(v_r_3164_, 3);
lean_dec(v_unused_3278_);
v___x_3265_ = v_r_3164_;
v_isShared_3266_ = v_isSharedCheck_3276_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_v_3263_);
lean_inc(v_k_3262_);
lean_inc(v_size_3261_);
lean_dec(v_r_3164_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3276_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_size_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
v_size_3267_ = lean_ctor_get(v_l_3259_, 0);
v___x_3268_ = lean_nat_add(v___x_3170_, v_size_3261_);
lean_dec(v_size_3261_);
v___x_3269_ = lean_nat_add(v___x_3170_, v_size_3267_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v_l_3259_);
lean_ctor_set(v___x_3265_, 3, v_impl_3169_);
lean_ctor_set(v___x_3265_, 2, v_v_3162_);
lean_ctor_set(v___x_3265_, 1, v_k_3161_);
lean_ctor_set(v___x_3265_, 0, v___x_3269_);
v___x_3271_ = v___x_3265_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3275_, 3, v_impl_3169_);
lean_ctor_set(v_reuseFailAlloc_3275_, 4, v_l_3259_);
v___x_3271_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3273_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_r_3260_);
lean_ctor_set(v___x_3166_, 3, v___x_3271_);
lean_ctor_set(v___x_3166_, 2, v_v_3263_);
lean_ctor_set(v___x_3166_, 1, v_k_3262_);
lean_ctor_set(v___x_3166_, 0, v___x_3268_);
v___x_3273_ = v___x_3166_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3268_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_k_3262_);
lean_ctor_set(v_reuseFailAlloc_3274_, 2, v_v_3263_);
lean_ctor_set(v_reuseFailAlloc_3274_, 3, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3274_, 4, v_r_3260_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
else
{
lean_object* v_k_3279_; lean_object* v_v_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3303_; 
v_k_3279_ = lean_ctor_get(v_r_3164_, 1);
v_v_3280_ = lean_ctor_get(v_r_3164_, 2);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; 
v_unused_3304_ = lean_ctor_get(v_r_3164_, 4);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_r_3164_, 3);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_r_3164_, 0);
lean_dec(v_unused_3306_);
v___x_3282_ = v_r_3164_;
v_isShared_3283_ = v_isSharedCheck_3303_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_v_3280_);
lean_inc(v_k_3279_);
lean_dec(v_r_3164_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3303_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v_k_3284_; lean_object* v_v_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3299_; 
v_k_3284_ = lean_ctor_get(v_l_3259_, 1);
v_v_3285_ = lean_ctor_get(v_l_3259_, 2);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_l_3259_);
if (v_isSharedCheck_3299_ == 0)
{
lean_object* v_unused_3300_; lean_object* v_unused_3301_; lean_object* v_unused_3302_; 
v_unused_3300_ = lean_ctor_get(v_l_3259_, 4);
lean_dec(v_unused_3300_);
v_unused_3301_ = lean_ctor_get(v_l_3259_, 3);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_l_3259_, 0);
lean_dec(v_unused_3302_);
v___x_3287_ = v_l_3259_;
v_isShared_3288_ = v_isSharedCheck_3299_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_v_3285_);
lean_inc(v_k_3284_);
lean_dec(v_l_3259_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3299_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = lean_unsigned_to_nat(3u);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 4, v_r_3260_);
lean_ctor_set(v___x_3287_, 3, v_r_3260_);
lean_ctor_set(v___x_3287_, 2, v_v_3162_);
lean_ctor_set(v___x_3287_, 1, v_k_3161_);
lean_ctor_set(v___x_3287_, 0, v___x_3170_);
v___x_3291_ = v___x_3287_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3298_, 3, v_r_3260_);
lean_ctor_set(v_reuseFailAlloc_3298_, 4, v_r_3260_);
v___x_3291_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3293_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 3, v_r_3260_);
lean_ctor_set(v___x_3282_, 0, v___x_3170_);
v___x_3293_ = v___x_3282_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_k_3279_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_v_3280_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v_r_3260_);
lean_ctor_set(v_reuseFailAlloc_3297_, 4, v_r_3260_);
v___x_3293_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3295_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v___x_3293_);
lean_ctor_set(v___x_3166_, 3, v___x_3291_);
lean_ctor_set(v___x_3166_, 2, v_v_3285_);
lean_ctor_set(v___x_3166_, 1, v_k_3284_);
lean_ctor_set(v___x_3166_, 0, v___x_3289_);
v___x_3295_ = v___x_3166_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3289_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_k_3284_);
lean_ctor_set(v_reuseFailAlloc_3296_, 2, v_v_3285_);
lean_ctor_set(v_reuseFailAlloc_3296_, 3, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3296_, 4, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3307_; 
v_r_3307_ = lean_ctor_get(v_r_3164_, 4);
lean_inc(v_r_3307_);
if (lean_obj_tag(v_r_3307_) == 0)
{
lean_object* v_k_3308_; lean_object* v_v_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3320_; 
v_k_3308_ = lean_ctor_get(v_r_3164_, 1);
v_v_3309_ = lean_ctor_get(v_r_3164_, 2);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; lean_object* v_unused_3322_; lean_object* v_unused_3323_; 
v_unused_3321_ = lean_ctor_get(v_r_3164_, 4);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v_r_3164_, 3);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v_r_3164_, 0);
lean_dec(v_unused_3323_);
v___x_3311_ = v_r_3164_;
v_isShared_3312_ = v_isSharedCheck_3320_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_v_3309_);
lean_inc(v_k_3308_);
lean_dec(v_r_3164_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3320_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3313_ = lean_unsigned_to_nat(3u);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 4, v_l_3259_);
lean_ctor_set(v___x_3311_, 2, v_v_3162_);
lean_ctor_set(v___x_3311_, 1, v_k_3161_);
lean_ctor_set(v___x_3311_, 0, v___x_3170_);
v___x_3315_ = v___x_3311_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3319_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3319_, 3, v_l_3259_);
lean_ctor_set(v_reuseFailAlloc_3319_, 4, v_l_3259_);
v___x_3315_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3317_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_r_3307_);
lean_ctor_set(v___x_3166_, 3, v___x_3315_);
lean_ctor_set(v___x_3166_, 2, v_v_3309_);
lean_ctor_set(v___x_3166_, 1, v_k_3308_);
lean_ctor_set(v___x_3166_, 0, v___x_3313_);
v___x_3317_ = v___x_3166_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_k_3308_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_v_3309_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v_r_3307_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_size_3324_; lean_object* v_k_3325_; lean_object* v_v_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3337_; 
v_size_3324_ = lean_ctor_get(v_r_3164_, 0);
v_k_3325_ = lean_ctor_get(v_r_3164_, 1);
v_v_3326_ = lean_ctor_get(v_r_3164_, 2);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; lean_object* v_unused_3339_; 
v_unused_3338_ = lean_ctor_get(v_r_3164_, 4);
lean_dec(v_unused_3338_);
v_unused_3339_ = lean_ctor_get(v_r_3164_, 3);
lean_dec(v_unused_3339_);
v___x_3328_ = v_r_3164_;
v_isShared_3329_ = v_isSharedCheck_3337_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_v_3326_);
lean_inc(v_k_3325_);
lean_inc(v_size_3324_);
lean_dec(v_r_3164_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3337_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 3, v_r_3307_);
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_size_3324_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_k_3325_);
lean_ctor_set(v_reuseFailAlloc_3336_, 2, v_v_3326_);
lean_ctor_set(v_reuseFailAlloc_3336_, 3, v_r_3307_);
lean_ctor_set(v_reuseFailAlloc_3336_, 4, v_r_3307_);
v___x_3331_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3332_ = lean_unsigned_to_nat(2u);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v___x_3331_);
lean_ctor_set(v___x_3166_, 3, v_r_3307_);
lean_ctor_set(v___x_3166_, 0, v___x_3332_);
v___x_3334_ = v___x_3166_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_r_3307_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v___x_3331_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
}
else
{
lean_object* v___x_3341_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 3, v_r_3164_);
lean_ctor_set(v___x_3166_, 0, v___x_3170_);
v___x_3341_ = v___x_3166_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3342_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3342_, 3, v_r_3164_);
lean_ctor_set(v_reuseFailAlloc_3342_, 4, v_r_3164_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3166_);
lean_dec(v_v_3162_);
lean_dec(v_k_3161_);
if (lean_obj_tag(v_l_3163_) == 0)
{
if (lean_obj_tag(v_r_3164_) == 0)
{
lean_object* v_size_3343_; lean_object* v_k_3344_; lean_object* v_v_3345_; lean_object* v_l_3346_; lean_object* v_r_3347_; lean_object* v_size_3348_; lean_object* v_k_3349_; lean_object* v_v_3350_; lean_object* v_l_3351_; lean_object* v_r_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
v_size_3343_ = lean_ctor_get(v_l_3163_, 0);
v_k_3344_ = lean_ctor_get(v_l_3163_, 1);
v_v_3345_ = lean_ctor_get(v_l_3163_, 2);
v_l_3346_ = lean_ctor_get(v_l_3163_, 3);
v_r_3347_ = lean_ctor_get(v_l_3163_, 4);
lean_inc(v_r_3347_);
v_size_3348_ = lean_ctor_get(v_r_3164_, 0);
v_k_3349_ = lean_ctor_get(v_r_3164_, 1);
v_v_3350_ = lean_ctor_get(v_r_3164_, 2);
v_l_3351_ = lean_ctor_get(v_r_3164_, 3);
lean_inc(v_l_3351_);
v_r_3352_ = lean_ctor_get(v_r_3164_, 4);
v___x_3353_ = lean_unsigned_to_nat(1u);
v___x_3354_ = lean_nat_dec_lt(v_size_3343_, v_size_3348_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3490_; 
lean_inc(v_l_3346_);
lean_inc(v_v_3345_);
lean_inc(v_k_3344_);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_l_3163_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; lean_object* v_unused_3492_; lean_object* v_unused_3493_; lean_object* v_unused_3494_; lean_object* v_unused_3495_; 
v_unused_3491_ = lean_ctor_get(v_l_3163_, 4);
lean_dec(v_unused_3491_);
v_unused_3492_ = lean_ctor_get(v_l_3163_, 3);
lean_dec(v_unused_3492_);
v_unused_3493_ = lean_ctor_get(v_l_3163_, 2);
lean_dec(v_unused_3493_);
v_unused_3494_ = lean_ctor_get(v_l_3163_, 1);
lean_dec(v_unused_3494_);
v_unused_3495_ = lean_ctor_get(v_l_3163_, 0);
lean_dec(v_unused_3495_);
v___x_3356_ = v_l_3163_;
v_isShared_3357_ = v_isSharedCheck_3490_;
goto v_resetjp_3355_;
}
else
{
lean_dec(v_l_3163_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3490_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v_tree_3359_; 
v___x_3358_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3344_, v_v_3345_, v_l_3346_, v_r_3347_);
v_tree_3359_ = lean_ctor_get(v___x_3358_, 2);
lean_inc(v_tree_3359_);
if (lean_obj_tag(v_tree_3359_) == 0)
{
lean_object* v_k_3360_; lean_object* v_v_3361_; lean_object* v_size_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v_k_3360_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_k_3360_);
v_v_3361_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_v_3361_);
lean_dec_ref(v___x_3358_);
v_size_3362_ = lean_ctor_get(v_tree_3359_, 0);
v___x_3363_ = lean_unsigned_to_nat(3u);
v___x_3364_ = lean_nat_mul(v___x_3363_, v_size_3362_);
v___x_3365_ = lean_nat_dec_lt(v___x_3364_, v_size_3348_);
lean_dec(v___x_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
lean_dec(v_l_3351_);
v___x_3366_ = lean_nat_add(v___x_3353_, v_size_3362_);
v___x_3367_ = lean_nat_add(v___x_3366_, v_size_3348_);
lean_dec(v___x_3366_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 4, v_r_3164_);
lean_ctor_set(v___x_3356_, 3, v_tree_3359_);
lean_ctor_set(v___x_3356_, 2, v_v_3361_);
lean_ctor_set(v___x_3356_, 1, v_k_3360_);
lean_ctor_set(v___x_3356_, 0, v___x_3367_);
v___x_3369_ = v___x_3356_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3360_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_v_3361_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_tree_3359_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_r_3164_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
else
{
lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3425_; 
lean_inc(v_r_3352_);
lean_inc(v_v_3350_);
lean_inc(v_k_3349_);
lean_inc(v_size_3348_);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; lean_object* v_unused_3427_; lean_object* v_unused_3428_; lean_object* v_unused_3429_; lean_object* v_unused_3430_; 
v_unused_3426_ = lean_ctor_get(v_r_3164_, 4);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_r_3164_, 3);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_r_3164_, 2);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v_r_3164_, 1);
lean_dec(v_unused_3429_);
v_unused_3430_ = lean_ctor_get(v_r_3164_, 0);
lean_dec(v_unused_3430_);
v___x_3372_ = v_r_3164_;
v_isShared_3373_ = v_isSharedCheck_3425_;
goto v_resetjp_3371_;
}
else
{
lean_dec(v_r_3164_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3425_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v_size_3374_; lean_object* v_k_3375_; lean_object* v_v_3376_; lean_object* v_l_3377_; lean_object* v_r_3378_; lean_object* v_size_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v_size_3374_ = lean_ctor_get(v_l_3351_, 0);
v_k_3375_ = lean_ctor_get(v_l_3351_, 1);
v_v_3376_ = lean_ctor_get(v_l_3351_, 2);
v_l_3377_ = lean_ctor_get(v_l_3351_, 3);
v_r_3378_ = lean_ctor_get(v_l_3351_, 4);
v_size_3379_ = lean_ctor_get(v_r_3352_, 0);
v___x_3380_ = lean_unsigned_to_nat(2u);
v___x_3381_ = lean_nat_mul(v___x_3380_, v_size_3379_);
v___x_3382_ = lean_nat_dec_lt(v_size_3374_, v___x_3381_);
lean_dec(v___x_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3410_; 
lean_inc(v_r_3378_);
lean_inc(v_l_3377_);
lean_inc(v_v_3376_);
lean_inc(v_k_3375_);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_l_3351_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; lean_object* v_unused_3412_; lean_object* v_unused_3413_; lean_object* v_unused_3414_; lean_object* v_unused_3415_; 
v_unused_3411_ = lean_ctor_get(v_l_3351_, 4);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_l_3351_, 3);
lean_dec(v_unused_3412_);
v_unused_3413_ = lean_ctor_get(v_l_3351_, 2);
lean_dec(v_unused_3413_);
v_unused_3414_ = lean_ctor_get(v_l_3351_, 1);
lean_dec(v_unused_3414_);
v_unused_3415_ = lean_ctor_get(v_l_3351_, 0);
lean_dec(v_unused_3415_);
v___x_3384_ = v_l_3351_;
v_isShared_3385_ = v_isSharedCheck_3410_;
goto v_resetjp_3383_;
}
else
{
lean_dec(v_l_3351_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3410_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3400_; 
v___x_3386_ = lean_nat_add(v___x_3353_, v_size_3362_);
v___x_3387_ = lean_nat_add(v___x_3386_, v_size_3348_);
lean_dec(v_size_3348_);
if (lean_obj_tag(v_l_3377_) == 0)
{
lean_object* v_size_3408_; 
v_size_3408_ = lean_ctor_get(v_l_3377_, 0);
lean_inc(v_size_3408_);
v___y_3400_ = v_size_3408_;
goto v___jp_3399_;
}
else
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_unsigned_to_nat(0u);
v___y_3400_ = v___x_3409_;
goto v___jp_3399_;
}
v___jp_3388_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_nat_add(v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 4, v_r_3352_);
lean_ctor_set(v___x_3384_, 3, v_r_3378_);
lean_ctor_set(v___x_3384_, 2, v_v_3350_);
lean_ctor_set(v___x_3384_, 1, v_k_3349_);
lean_ctor_set(v___x_3384_, 0, v___x_3392_);
v___x_3394_ = v___x_3384_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_k_3349_);
lean_ctor_set(v_reuseFailAlloc_3398_, 2, v_v_3350_);
lean_ctor_set(v_reuseFailAlloc_3398_, 3, v_r_3378_);
lean_ctor_set(v_reuseFailAlloc_3398_, 4, v_r_3352_);
v___x_3394_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3396_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 4, v___x_3394_);
lean_ctor_set(v___x_3372_, 3, v___y_3389_);
lean_ctor_set(v___x_3372_, 2, v_v_3376_);
lean_ctor_set(v___x_3372_, 1, v_k_3375_);
lean_ctor_set(v___x_3372_, 0, v___x_3387_);
v___x_3396_ = v___x_3372_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_k_3375_);
lean_ctor_set(v_reuseFailAlloc_3397_, 2, v_v_3376_);
lean_ctor_set(v_reuseFailAlloc_3397_, 3, v___y_3389_);
lean_ctor_set(v_reuseFailAlloc_3397_, 4, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
v___jp_3399_:
{
lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3401_ = lean_nat_add(v___x_3386_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec(v___x_3386_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 4, v_l_3377_);
lean_ctor_set(v___x_3356_, 3, v_tree_3359_);
lean_ctor_set(v___x_3356_, 2, v_v_3361_);
lean_ctor_set(v___x_3356_, 1, v_k_3360_);
lean_ctor_set(v___x_3356_, 0, v___x_3401_);
v___x_3403_ = v___x_3356_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_k_3360_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v_v_3361_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v_tree_3359_);
lean_ctor_set(v_reuseFailAlloc_3407_, 4, v_l_3377_);
v___x_3403_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_nat_add(v___x_3353_, v_size_3379_);
if (lean_obj_tag(v_r_3378_) == 0)
{
lean_object* v_size_3405_; 
v_size_3405_ = lean_ctor_get(v_r_3378_, 0);
lean_inc(v_size_3405_);
v___y_3389_ = v___x_3403_;
v___y_3390_ = v___x_3404_;
v___y_3391_ = v_size_3405_;
goto v___jp_3388_;
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_unsigned_to_nat(0u);
v___y_3389_ = v___x_3403_;
v___y_3390_ = v___x_3404_;
v___y_3391_ = v___x_3406_;
goto v___jp_3388_;
}
}
}
}
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3416_ = lean_nat_add(v___x_3353_, v_size_3362_);
v___x_3417_ = lean_nat_add(v___x_3416_, v_size_3348_);
lean_dec(v_size_3348_);
v___x_3418_ = lean_nat_add(v___x_3416_, v_size_3374_);
lean_dec(v___x_3416_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 4, v_l_3351_);
lean_ctor_set(v___x_3372_, 3, v_tree_3359_);
lean_ctor_set(v___x_3372_, 2, v_v_3361_);
lean_ctor_set(v___x_3372_, 1, v_k_3360_);
lean_ctor_set(v___x_3372_, 0, v___x_3418_);
v___x_3420_ = v___x_3372_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3360_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3361_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_tree_3359_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_l_3351_);
v___x_3420_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 4, v_r_3352_);
lean_ctor_set(v___x_3356_, 3, v___x_3420_);
lean_ctor_set(v___x_3356_, 2, v_v_3350_);
lean_ctor_set(v___x_3356_, 1, v_k_3349_);
lean_ctor_set(v___x_3356_, 0, v___x_3417_);
v___x_3422_ = v___x_3356_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_k_3349_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_v_3350_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v_r_3352_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
}
else
{
lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3484_; 
lean_inc(v_r_3352_);
lean_inc(v_v_3350_);
lean_inc(v_k_3349_);
lean_inc(v_size_3348_);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; lean_object* v_unused_3486_; lean_object* v_unused_3487_; lean_object* v_unused_3488_; lean_object* v_unused_3489_; 
v_unused_3485_ = lean_ctor_get(v_r_3164_, 4);
lean_dec(v_unused_3485_);
v_unused_3486_ = lean_ctor_get(v_r_3164_, 3);
lean_dec(v_unused_3486_);
v_unused_3487_ = lean_ctor_get(v_r_3164_, 2);
lean_dec(v_unused_3487_);
v_unused_3488_ = lean_ctor_get(v_r_3164_, 1);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_r_3164_, 0);
lean_dec(v_unused_3489_);
v___x_3432_ = v_r_3164_;
v_isShared_3433_ = v_isSharedCheck_3484_;
goto v_resetjp_3431_;
}
else
{
lean_dec(v_r_3164_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3484_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
if (lean_obj_tag(v_l_3351_) == 0)
{
if (lean_obj_tag(v_r_3352_) == 0)
{
lean_object* v_k_3434_; lean_object* v_v_3435_; lean_object* v_size_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v_k_3434_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_k_3434_);
v_v_3435_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_v_3435_);
lean_dec_ref(v___x_3358_);
v_size_3436_ = lean_ctor_get(v_l_3351_, 0);
v___x_3437_ = lean_nat_add(v___x_3353_, v_size_3348_);
lean_dec(v_size_3348_);
v___x_3438_ = lean_nat_add(v___x_3353_, v_size_3436_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v_l_3351_);
lean_ctor_set(v___x_3432_, 3, v_tree_3359_);
lean_ctor_set(v___x_3432_, 2, v_v_3435_);
lean_ctor_set(v___x_3432_, 1, v_k_3434_);
lean_ctor_set(v___x_3432_, 0, v___x_3438_);
v___x_3440_ = v___x_3432_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_k_3434_);
lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_v_3435_);
lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_tree_3359_);
lean_ctor_set(v_reuseFailAlloc_3444_, 4, v_l_3351_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 4, v_r_3352_);
lean_ctor_set(v___x_3356_, 3, v___x_3440_);
lean_ctor_set(v___x_3356_, 2, v_v_3350_);
lean_ctor_set(v___x_3356_, 1, v_k_3349_);
lean_ctor_set(v___x_3356_, 0, v___x_3437_);
v___x_3442_ = v___x_3356_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_k_3349_);
lean_ctor_set(v_reuseFailAlloc_3443_, 2, v_v_3350_);
lean_ctor_set(v_reuseFailAlloc_3443_, 3, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3443_, 4, v_r_3352_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
else
{
lean_object* v_k_3445_; lean_object* v_v_3446_; lean_object* v_k_3447_; lean_object* v_v_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3462_; 
lean_dec(v_size_3348_);
v_k_3445_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_k_3445_);
v_v_3446_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_v_3446_);
lean_dec_ref(v___x_3358_);
v_k_3447_ = lean_ctor_get(v_l_3351_, 1);
v_v_3448_ = lean_ctor_get(v_l_3351_, 2);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_l_3351_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; lean_object* v_unused_3464_; lean_object* v_unused_3465_; 
v_unused_3463_ = lean_ctor_get(v_l_3351_, 4);
lean_dec(v_unused_3463_);
v_unused_3464_ = lean_ctor_get(v_l_3351_, 3);
lean_dec(v_unused_3464_);
v_unused_3465_ = lean_ctor_get(v_l_3351_, 0);
lean_dec(v_unused_3465_);
v___x_3450_ = v_l_3351_;
v_isShared_3451_ = v_isSharedCheck_3462_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_v_3448_);
lean_inc(v_k_3447_);
lean_dec(v_l_3351_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3462_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3452_ = lean_unsigned_to_nat(3u);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 4, v_r_3352_);
lean_ctor_set(v___x_3450_, 3, v_r_3352_);
lean_ctor_set(v___x_3450_, 2, v_v_3446_);
lean_ctor_set(v___x_3450_, 1, v_k_3445_);
lean_ctor_set(v___x_3450_, 0, v___x_3353_);
v___x_3454_ = v___x_3450_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_k_3445_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_v_3446_);
lean_ctor_set(v_reuseFailAlloc_3461_, 3, v_r_3352_);
lean_ctor_set(v_reuseFailAlloc_3461_, 4, v_r_3352_);
v___x_3454_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3456_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 3, v_r_3352_);
lean_ctor_set(v___x_3432_, 0, v___x_3353_);
v___x_3456_ = v___x_3432_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_k_3349_);
lean_ctor_set(v_reuseFailAlloc_3460_, 2, v_v_3350_);
lean_ctor_set(v_reuseFailAlloc_3460_, 3, v_r_3352_);
lean_ctor_set(v_reuseFailAlloc_3460_, 4, v_r_3352_);
v___x_3456_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3458_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 4, v___x_3456_);
lean_ctor_set(v___x_3356_, 3, v___x_3454_);
lean_ctor_set(v___x_3356_, 2, v_v_3448_);
lean_ctor_set(v___x_3356_, 1, v_k_3447_);
lean_ctor_set(v___x_3356_, 0, v___x_3452_);
v___x_3458_ = v___x_3356_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_k_3447_);
lean_ctor_set(v_reuseFailAlloc_3459_, 2, v_v_3448_);
lean_ctor_set(v_reuseFailAlloc_3459_, 3, v___x_3454_);
lean_ctor_set(v_reuseFailAlloc_3459_, 4, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3352_) == 0)
{
lean_object* v_k_3466_; lean_object* v_v_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
lean_dec(v_size_3348_);
v_k_3466_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_k_3466_);
v_v_3467_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_v_3467_);
lean_dec_ref(v___x_3358_);
v___x_3468_ = lean_unsigned_to_nat(3u);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v_l_3351_);
lean_ctor_set(v___x_3432_, 2, v_v_3467_);
lean_ctor_set(v___x_3432_, 1, v_k_3466_);
lean_ctor_set(v___x_3432_, 0, v___x_3353_);
v___x_3470_ = v___x_3432_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_k_3466_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_v_3467_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v_l_3351_);
lean_ctor_set(v_reuseFailAlloc_3474_, 4, v_l_3351_);
v___x_3470_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 4, v_r_3352_);
lean_ctor_set(v___x_3356_, 3, v___x_3470_);
lean_ctor_set(v___x_3356_, 2, v_v_3350_);
lean_ctor_set(v___x_3356_, 1, v_k_3349_);
lean_ctor_set(v___x_3356_, 0, v___x_3468_);
v___x_3472_ = v___x_3356_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_k_3349_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_v_3350_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v_r_3352_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
else
{
lean_object* v_k_3475_; lean_object* v_v_3476_; lean_object* v___x_3478_; 
v_k_3475_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_k_3475_);
v_v_3476_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_v_3476_);
lean_dec_ref(v___x_3358_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 3, v_r_3352_);
v___x_3478_ = v___x_3432_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_size_3348_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_k_3349_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_v_3350_);
lean_ctor_set(v_reuseFailAlloc_3483_, 3, v_r_3352_);
lean_ctor_set(v_reuseFailAlloc_3483_, 4, v_r_3352_);
v___x_3478_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3479_ = lean_unsigned_to_nat(2u);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 4, v___x_3478_);
lean_ctor_set(v___x_3356_, 3, v_r_3352_);
lean_ctor_set(v___x_3356_, 2, v_v_3476_);
lean_ctor_set(v___x_3356_, 1, v_k_3475_);
lean_ctor_set(v___x_3356_, 0, v___x_3479_);
v___x_3481_ = v___x_3356_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_k_3475_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_v_3476_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v_r_3352_);
lean_ctor_set(v_reuseFailAlloc_3482_, 4, v___x_3478_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
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
lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3648_; 
lean_inc(v_r_3352_);
lean_inc(v_v_3350_);
lean_inc(v_k_3349_);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_r_3164_);
if (v_isSharedCheck_3648_ == 0)
{
lean_object* v_unused_3649_; lean_object* v_unused_3650_; lean_object* v_unused_3651_; lean_object* v_unused_3652_; lean_object* v_unused_3653_; 
v_unused_3649_ = lean_ctor_get(v_r_3164_, 4);
lean_dec(v_unused_3649_);
v_unused_3650_ = lean_ctor_get(v_r_3164_, 3);
lean_dec(v_unused_3650_);
v_unused_3651_ = lean_ctor_get(v_r_3164_, 2);
lean_dec(v_unused_3651_);
v_unused_3652_ = lean_ctor_get(v_r_3164_, 1);
lean_dec(v_unused_3652_);
v_unused_3653_ = lean_ctor_get(v_r_3164_, 0);
lean_dec(v_unused_3653_);
v___x_3497_ = v_r_3164_;
v_isShared_3498_ = v_isSharedCheck_3648_;
goto v_resetjp_3496_;
}
else
{
lean_dec(v_r_3164_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3648_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; lean_object* v_tree_3500_; 
v___x_3499_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3349_, v_v_3350_, v_l_3351_, v_r_3352_);
v_tree_3500_ = lean_ctor_get(v___x_3499_, 2);
lean_inc(v_tree_3500_);
if (lean_obj_tag(v_tree_3500_) == 0)
{
lean_object* v_k_3501_; lean_object* v_v_3502_; lean_object* v_size_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_k_3501_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_k_3501_);
v_v_3502_ = lean_ctor_get(v___x_3499_, 1);
lean_inc(v_v_3502_);
lean_dec_ref(v___x_3499_);
v_size_3503_ = lean_ctor_get(v_tree_3500_, 0);
v___x_3504_ = lean_unsigned_to_nat(3u);
v___x_3505_ = lean_nat_mul(v___x_3504_, v_size_3503_);
v___x_3506_ = lean_nat_dec_lt(v___x_3505_, v_size_3343_);
lean_dec(v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3510_; 
lean_dec(v_r_3347_);
v___x_3507_ = lean_nat_add(v___x_3353_, v_size_3343_);
v___x_3508_ = lean_nat_add(v___x_3507_, v_size_3503_);
lean_dec(v___x_3507_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 4, v_tree_3500_);
lean_ctor_set(v___x_3497_, 3, v_l_3163_);
lean_ctor_set(v___x_3497_, 2, v_v_3502_);
lean_ctor_set(v___x_3497_, 1, v_k_3501_);
lean_ctor_set(v___x_3497_, 0, v___x_3508_);
v___x_3510_ = v___x_3497_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_k_3501_);
lean_ctor_set(v_reuseFailAlloc_3511_, 2, v_v_3502_);
lean_ctor_set(v_reuseFailAlloc_3511_, 3, v_l_3163_);
lean_ctor_set(v_reuseFailAlloc_3511_, 4, v_tree_3500_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
else
{
lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3577_; 
lean_inc(v_l_3346_);
lean_inc(v_v_3345_);
lean_inc(v_k_3344_);
lean_inc(v_size_3343_);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_l_3163_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; lean_object* v_unused_3582_; 
v_unused_3578_ = lean_ctor_get(v_l_3163_, 4);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_l_3163_, 3);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_l_3163_, 2);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_l_3163_, 1);
lean_dec(v_unused_3581_);
v_unused_3582_ = lean_ctor_get(v_l_3163_, 0);
lean_dec(v_unused_3582_);
v___x_3513_ = v_l_3163_;
v_isShared_3514_ = v_isSharedCheck_3577_;
goto v_resetjp_3512_;
}
else
{
lean_dec(v_l_3163_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3577_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_size_3515_; lean_object* v_size_3516_; lean_object* v_k_3517_; lean_object* v_v_3518_; lean_object* v_l_3519_; lean_object* v_r_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v_size_3515_ = lean_ctor_get(v_l_3346_, 0);
v_size_3516_ = lean_ctor_get(v_r_3347_, 0);
v_k_3517_ = lean_ctor_get(v_r_3347_, 1);
v_v_3518_ = lean_ctor_get(v_r_3347_, 2);
v_l_3519_ = lean_ctor_get(v_r_3347_, 3);
v_r_3520_ = lean_ctor_get(v_r_3347_, 4);
v___x_3521_ = lean_unsigned_to_nat(2u);
v___x_3522_ = lean_nat_mul(v___x_3521_, v_size_3515_);
v___x_3523_ = lean_nat_dec_lt(v_size_3516_, v___x_3522_);
lean_dec(v___x_3522_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3561_; 
lean_inc(v_r_3520_);
lean_inc(v_l_3519_);
lean_inc(v_v_3518_);
lean_inc(v_k_3517_);
lean_del_object(v___x_3513_);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_r_3347_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; lean_object* v_unused_3563_; lean_object* v_unused_3564_; lean_object* v_unused_3565_; lean_object* v_unused_3566_; 
v_unused_3562_ = lean_ctor_get(v_r_3347_, 4);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_r_3347_, 3);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_r_3347_, 2);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_r_3347_, 1);
lean_dec(v_unused_3565_);
v_unused_3566_ = lean_ctor_get(v_r_3347_, 0);
lean_dec(v_unused_3566_);
v___x_3525_ = v_r_3347_;
v_isShared_3526_ = v_isSharedCheck_3561_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v_r_3347_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3561_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___x_3549_; lean_object* v___y_3551_; 
v___x_3527_ = lean_nat_add(v___x_3353_, v_size_3343_);
lean_dec(v_size_3343_);
v___x_3528_ = lean_nat_add(v___x_3527_, v_size_3503_);
lean_dec(v___x_3527_);
v___x_3549_ = lean_nat_add(v___x_3353_, v_size_3515_);
if (lean_obj_tag(v_l_3519_) == 0)
{
lean_object* v_size_3559_; 
v_size_3559_ = lean_ctor_get(v_l_3519_, 0);
lean_inc(v_size_3559_);
v___y_3551_ = v_size_3559_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_unsigned_to_nat(0u);
v___y_3551_ = v___x_3560_;
goto v___jp_3550_;
}
v___jp_3529_:
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = lean_nat_add(v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec(v___y_3531_);
lean_inc_ref(v_tree_3500_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 4, v_tree_3500_);
lean_ctor_set(v___x_3525_, 3, v_r_3520_);
lean_ctor_set(v___x_3525_, 2, v_v_3502_);
lean_ctor_set(v___x_3525_, 1, v_k_3501_);
lean_ctor_set(v___x_3525_, 0, v___x_3533_);
v___x_3535_ = v___x_3525_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3501_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_v_3502_);
lean_ctor_set(v_reuseFailAlloc_3548_, 3, v_r_3520_);
lean_ctor_set(v_reuseFailAlloc_3548_, 4, v_tree_3500_);
v___x_3535_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_isSharedCheck_3542_ = !lean_is_exclusive(v_tree_3500_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; lean_object* v_unused_3544_; lean_object* v_unused_3545_; lean_object* v_unused_3546_; lean_object* v_unused_3547_; 
v_unused_3543_ = lean_ctor_get(v_tree_3500_, 4);
lean_dec(v_unused_3543_);
v_unused_3544_ = lean_ctor_get(v_tree_3500_, 3);
lean_dec(v_unused_3544_);
v_unused_3545_ = lean_ctor_get(v_tree_3500_, 2);
lean_dec(v_unused_3545_);
v_unused_3546_ = lean_ctor_get(v_tree_3500_, 1);
lean_dec(v_unused_3546_);
v_unused_3547_ = lean_ctor_get(v_tree_3500_, 0);
lean_dec(v_unused_3547_);
v___x_3537_ = v_tree_3500_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v_tree_3500_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 4, v___x_3535_);
lean_ctor_set(v___x_3537_, 3, v___y_3530_);
lean_ctor_set(v___x_3537_, 2, v_v_3518_);
lean_ctor_set(v___x_3537_, 1, v_k_3517_);
lean_ctor_set(v___x_3537_, 0, v___x_3528_);
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_k_3517_);
lean_ctor_set(v_reuseFailAlloc_3541_, 2, v_v_3518_);
lean_ctor_set(v_reuseFailAlloc_3541_, 3, v___y_3530_);
lean_ctor_set(v_reuseFailAlloc_3541_, 4, v___x_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
v___jp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3552_ = lean_nat_add(v___x_3549_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec(v___x_3549_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 4, v_l_3519_);
lean_ctor_set(v___x_3497_, 3, v_l_3346_);
lean_ctor_set(v___x_3497_, 2, v_v_3345_);
lean_ctor_set(v___x_3497_, 1, v_k_3344_);
lean_ctor_set(v___x_3497_, 0, v___x_3552_);
v___x_3554_ = v___x_3497_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3552_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_k_3344_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_v_3345_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_l_3346_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v_l_3519_);
v___x_3554_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_nat_add(v___x_3353_, v_size_3503_);
if (lean_obj_tag(v_r_3520_) == 0)
{
lean_object* v_size_3556_; 
v_size_3556_ = lean_ctor_get(v_r_3520_, 0);
lean_inc(v_size_3556_);
v___y_3530_ = v___x_3554_;
v___y_3531_ = v___x_3555_;
v___y_3532_ = v_size_3556_;
goto v___jp_3529_;
}
else
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_unsigned_to_nat(0u);
v___y_3530_ = v___x_3554_;
v___y_3531_ = v___x_3555_;
v___y_3532_ = v___x_3557_;
goto v___jp_3529_;
}
}
}
}
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3567_ = lean_nat_add(v___x_3353_, v_size_3343_);
lean_dec(v_size_3343_);
v___x_3568_ = lean_nat_add(v___x_3567_, v_size_3503_);
lean_dec(v___x_3567_);
v___x_3569_ = lean_nat_add(v___x_3353_, v_size_3503_);
v___x_3570_ = lean_nat_add(v___x_3569_, v_size_3516_);
lean_dec(v___x_3569_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 4, v_tree_3500_);
lean_ctor_set(v___x_3497_, 3, v_r_3347_);
lean_ctor_set(v___x_3497_, 2, v_v_3502_);
lean_ctor_set(v___x_3497_, 1, v_k_3501_);
lean_ctor_set(v___x_3497_, 0, v___x_3570_);
v___x_3572_ = v___x_3497_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_k_3501_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v_v_3502_);
lean_ctor_set(v_reuseFailAlloc_3576_, 3, v_r_3347_);
lean_ctor_set(v_reuseFailAlloc_3576_, 4, v_tree_3500_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3574_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 4, v___x_3572_);
lean_ctor_set(v___x_3513_, 0, v___x_3568_);
v___x_3574_ = v___x_3513_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_k_3344_);
lean_ctor_set(v_reuseFailAlloc_3575_, 2, v_v_3345_);
lean_ctor_set(v_reuseFailAlloc_3575_, 3, v_l_3346_);
lean_ctor_set(v_reuseFailAlloc_3575_, 4, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3346_) == 0)
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3606_; 
lean_inc_ref(v_l_3346_);
lean_inc(v_v_3345_);
lean_inc(v_k_3344_);
lean_inc(v_size_3343_);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_l_3163_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; lean_object* v_unused_3608_; lean_object* v_unused_3609_; lean_object* v_unused_3610_; lean_object* v_unused_3611_; 
v_unused_3607_ = lean_ctor_get(v_l_3163_, 4);
lean_dec(v_unused_3607_);
v_unused_3608_ = lean_ctor_get(v_l_3163_, 3);
lean_dec(v_unused_3608_);
v_unused_3609_ = lean_ctor_get(v_l_3163_, 2);
lean_dec(v_unused_3609_);
v_unused_3610_ = lean_ctor_get(v_l_3163_, 1);
lean_dec(v_unused_3610_);
v_unused_3611_ = lean_ctor_get(v_l_3163_, 0);
lean_dec(v_unused_3611_);
v___x_3584_ = v_l_3163_;
v_isShared_3585_ = v_isSharedCheck_3606_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v_l_3163_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3606_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
if (lean_obj_tag(v_r_3347_) == 0)
{
lean_object* v_k_3586_; lean_object* v_v_3587_; lean_object* v_size_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v_k_3586_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_k_3586_);
v_v_3587_ = lean_ctor_get(v___x_3499_, 1);
lean_inc(v_v_3587_);
lean_dec_ref(v___x_3499_);
v_size_3588_ = lean_ctor_get(v_r_3347_, 0);
v___x_3589_ = lean_nat_add(v___x_3353_, v_size_3343_);
lean_dec(v_size_3343_);
v___x_3590_ = lean_nat_add(v___x_3353_, v_size_3588_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 4, v_tree_3500_);
lean_ctor_set(v___x_3497_, 3, v_r_3347_);
lean_ctor_set(v___x_3497_, 2, v_v_3587_);
lean_ctor_set(v___x_3497_, 1, v_k_3586_);
lean_ctor_set(v___x_3497_, 0, v___x_3590_);
v___x_3592_ = v___x_3497_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_k_3586_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_v_3587_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_r_3347_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_tree_3500_);
v___x_3592_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3594_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 4, v___x_3592_);
lean_ctor_set(v___x_3584_, 0, v___x_3589_);
v___x_3594_ = v___x_3584_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3589_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_k_3344_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_v_3345_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_l_3346_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
else
{
lean_object* v_k_3597_; lean_object* v_v_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
lean_dec(v_size_3343_);
v_k_3597_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_k_3597_);
v_v_3598_ = lean_ctor_get(v___x_3499_, 1);
lean_inc(v_v_3598_);
lean_dec_ref(v___x_3499_);
v___x_3599_ = lean_unsigned_to_nat(3u);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 4, v_r_3347_);
lean_ctor_set(v___x_3497_, 3, v_r_3347_);
lean_ctor_set(v___x_3497_, 2, v_v_3598_);
lean_ctor_set(v___x_3497_, 1, v_k_3597_);
lean_ctor_set(v___x_3497_, 0, v___x_3353_);
v___x_3601_ = v___x_3497_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_k_3597_);
lean_ctor_set(v_reuseFailAlloc_3605_, 2, v_v_3598_);
lean_ctor_set(v_reuseFailAlloc_3605_, 3, v_r_3347_);
lean_ctor_set(v_reuseFailAlloc_3605_, 4, v_r_3347_);
v___x_3601_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3603_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 4, v___x_3601_);
lean_ctor_set(v___x_3584_, 0, v___x_3599_);
v___x_3603_ = v___x_3584_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_k_3344_);
lean_ctor_set(v_reuseFailAlloc_3604_, 2, v_v_3345_);
lean_ctor_set(v_reuseFailAlloc_3604_, 3, v_l_3346_);
lean_ctor_set(v_reuseFailAlloc_3604_, 4, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3347_) == 0)
{
lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3636_; 
lean_inc(v_l_3346_);
lean_inc(v_v_3345_);
lean_inc(v_k_3344_);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_l_3163_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; lean_object* v_unused_3638_; lean_object* v_unused_3639_; lean_object* v_unused_3640_; lean_object* v_unused_3641_; 
v_unused_3637_ = lean_ctor_get(v_l_3163_, 4);
lean_dec(v_unused_3637_);
v_unused_3638_ = lean_ctor_get(v_l_3163_, 3);
lean_dec(v_unused_3638_);
v_unused_3639_ = lean_ctor_get(v_l_3163_, 2);
lean_dec(v_unused_3639_);
v_unused_3640_ = lean_ctor_get(v_l_3163_, 1);
lean_dec(v_unused_3640_);
v_unused_3641_ = lean_ctor_get(v_l_3163_, 0);
lean_dec(v_unused_3641_);
v___x_3613_ = v_l_3163_;
v_isShared_3614_ = v_isSharedCheck_3636_;
goto v_resetjp_3612_;
}
else
{
lean_dec(v_l_3163_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3636_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v_k_3615_; lean_object* v_v_3616_; lean_object* v_k_3617_; lean_object* v_v_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3632_; 
v_k_3615_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_k_3615_);
v_v_3616_ = lean_ctor_get(v___x_3499_, 1);
lean_inc(v_v_3616_);
lean_dec_ref(v___x_3499_);
v_k_3617_ = lean_ctor_get(v_r_3347_, 1);
v_v_3618_ = lean_ctor_get(v_r_3347_, 2);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_r_3347_);
if (v_isSharedCheck_3632_ == 0)
{
lean_object* v_unused_3633_; lean_object* v_unused_3634_; lean_object* v_unused_3635_; 
v_unused_3633_ = lean_ctor_get(v_r_3347_, 4);
lean_dec(v_unused_3633_);
v_unused_3634_ = lean_ctor_get(v_r_3347_, 3);
lean_dec(v_unused_3634_);
v_unused_3635_ = lean_ctor_get(v_r_3347_, 0);
lean_dec(v_unused_3635_);
v___x_3620_ = v_r_3347_;
v_isShared_3621_ = v_isSharedCheck_3632_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_v_3618_);
lean_inc(v_k_3617_);
lean_dec(v_r_3347_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3632_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3622_ = lean_unsigned_to_nat(3u);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 4, v_l_3346_);
lean_ctor_set(v___x_3620_, 3, v_l_3346_);
lean_ctor_set(v___x_3620_, 2, v_v_3345_);
lean_ctor_set(v___x_3620_, 1, v_k_3344_);
lean_ctor_set(v___x_3620_, 0, v___x_3353_);
v___x_3624_ = v___x_3620_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_k_3344_);
lean_ctor_set(v_reuseFailAlloc_3631_, 2, v_v_3345_);
lean_ctor_set(v_reuseFailAlloc_3631_, 3, v_l_3346_);
lean_ctor_set(v_reuseFailAlloc_3631_, 4, v_l_3346_);
v___x_3624_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3626_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 4, v_l_3346_);
lean_ctor_set(v___x_3497_, 3, v_l_3346_);
lean_ctor_set(v___x_3497_, 2, v_v_3616_);
lean_ctor_set(v___x_3497_, 1, v_k_3615_);
lean_ctor_set(v___x_3497_, 0, v___x_3353_);
v___x_3626_ = v___x_3497_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3615_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3616_);
lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_l_3346_);
lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_l_3346_);
v___x_3626_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3628_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 4, v___x_3626_);
lean_ctor_set(v___x_3613_, 3, v___x_3624_);
lean_ctor_set(v___x_3613_, 2, v_v_3618_);
lean_ctor_set(v___x_3613_, 1, v_k_3617_);
lean_ctor_set(v___x_3613_, 0, v___x_3622_);
v___x_3628_ = v___x_3613_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3622_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_k_3617_);
lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_v_3618_);
lean_ctor_set(v_reuseFailAlloc_3629_, 3, v___x_3624_);
lean_ctor_set(v_reuseFailAlloc_3629_, 4, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
}
else
{
lean_object* v_k_3642_; lean_object* v_v_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v_k_3642_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_k_3642_);
v_v_3643_ = lean_ctor_get(v___x_3499_, 1);
lean_inc(v_v_3643_);
lean_dec_ref(v___x_3499_);
v___x_3644_ = lean_unsigned_to_nat(2u);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 4, v_r_3347_);
lean_ctor_set(v___x_3497_, 3, v_l_3163_);
lean_ctor_set(v___x_3497_, 2, v_v_3643_);
lean_ctor_set(v___x_3497_, 1, v_k_3642_);
lean_ctor_set(v___x_3497_, 0, v___x_3644_);
v___x_3646_ = v___x_3497_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_k_3642_);
lean_ctor_set(v_reuseFailAlloc_3647_, 2, v_v_3643_);
lean_ctor_set(v_reuseFailAlloc_3647_, 3, v_l_3163_);
lean_ctor_set(v_reuseFailAlloc_3647_, 4, v_r_3347_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
}
}
else
{
return v_l_3163_;
}
}
else
{
return v_r_3164_;
}
}
default: 
{
lean_object* v_impl_3654_; lean_object* v___x_3655_; 
v_impl_3654_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3159_, v_r_3164_);
v___x_3655_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3654_) == 0)
{
if (lean_obj_tag(v_l_3163_) == 0)
{
lean_object* v_size_3656_; lean_object* v_size_3657_; lean_object* v_k_3658_; lean_object* v_v_3659_; lean_object* v_l_3660_; lean_object* v_r_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; uint8_t v___x_3664_; 
v_size_3656_ = lean_ctor_get(v_impl_3654_, 0);
lean_inc(v_size_3656_);
v_size_3657_ = lean_ctor_get(v_l_3163_, 0);
v_k_3658_ = lean_ctor_get(v_l_3163_, 1);
v_v_3659_ = lean_ctor_get(v_l_3163_, 2);
v_l_3660_ = lean_ctor_get(v_l_3163_, 3);
v_r_3661_ = lean_ctor_get(v_l_3163_, 4);
lean_inc(v_r_3661_);
v___x_3662_ = lean_unsigned_to_nat(3u);
v___x_3663_ = lean_nat_mul(v___x_3662_, v_size_3656_);
v___x_3664_ = lean_nat_dec_lt(v___x_3663_, v_size_3657_);
lean_dec(v___x_3663_);
if (v___x_3664_ == 0)
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3668_; 
lean_dec(v_r_3661_);
v___x_3665_ = lean_nat_add(v___x_3655_, v_size_3657_);
v___x_3666_ = lean_nat_add(v___x_3665_, v_size_3656_);
lean_dec(v_size_3656_);
lean_dec(v___x_3665_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_impl_3654_);
lean_ctor_set(v___x_3166_, 0, v___x_3666_);
v___x_3668_ = v___x_3166_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_l_3163_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v_impl_3654_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
else
{
lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3735_; 
lean_inc(v_l_3660_);
lean_inc(v_v_3659_);
lean_inc(v_k_3658_);
lean_inc(v_size_3657_);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_l_3163_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; lean_object* v_unused_3737_; lean_object* v_unused_3738_; lean_object* v_unused_3739_; lean_object* v_unused_3740_; 
v_unused_3736_ = lean_ctor_get(v_l_3163_, 4);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_l_3163_, 3);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_l_3163_, 2);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_l_3163_, 1);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_l_3163_, 0);
lean_dec(v_unused_3740_);
v___x_3671_ = v_l_3163_;
v_isShared_3672_ = v_isSharedCheck_3735_;
goto v_resetjp_3670_;
}
else
{
lean_dec(v_l_3163_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3735_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v_size_3673_; lean_object* v_size_3674_; lean_object* v_k_3675_; lean_object* v_v_3676_; lean_object* v_l_3677_; lean_object* v_r_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v_size_3673_ = lean_ctor_get(v_l_3660_, 0);
v_size_3674_ = lean_ctor_get(v_r_3661_, 0);
v_k_3675_ = lean_ctor_get(v_r_3661_, 1);
v_v_3676_ = lean_ctor_get(v_r_3661_, 2);
v_l_3677_ = lean_ctor_get(v_r_3661_, 3);
v_r_3678_ = lean_ctor_get(v_r_3661_, 4);
v___x_3679_ = lean_unsigned_to_nat(2u);
v___x_3680_ = lean_nat_mul(v___x_3679_, v_size_3673_);
v___x_3681_ = lean_nat_dec_lt(v_size_3674_, v___x_3680_);
lean_dec(v___x_3680_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3710_; 
lean_inc(v_r_3678_);
lean_inc(v_l_3677_);
lean_inc(v_v_3676_);
lean_inc(v_k_3675_);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_r_3661_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; lean_object* v_unused_3712_; lean_object* v_unused_3713_; lean_object* v_unused_3714_; lean_object* v_unused_3715_; 
v_unused_3711_ = lean_ctor_get(v_r_3661_, 4);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_r_3661_, 3);
lean_dec(v_unused_3712_);
v_unused_3713_ = lean_ctor_get(v_r_3661_, 2);
lean_dec(v_unused_3713_);
v_unused_3714_ = lean_ctor_get(v_r_3661_, 1);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_r_3661_, 0);
lean_dec(v_unused_3715_);
v___x_3683_ = v_r_3661_;
v_isShared_3684_ = v_isSharedCheck_3710_;
goto v_resetjp_3682_;
}
else
{
lean_dec(v_r_3661_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3710_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___x_3698_; lean_object* v___y_3700_; 
v___x_3685_ = lean_nat_add(v___x_3655_, v_size_3657_);
lean_dec(v_size_3657_);
v___x_3686_ = lean_nat_add(v___x_3685_, v_size_3656_);
lean_dec(v___x_3685_);
v___x_3698_ = lean_nat_add(v___x_3655_, v_size_3673_);
if (lean_obj_tag(v_l_3677_) == 0)
{
lean_object* v_size_3708_; 
v_size_3708_ = lean_ctor_get(v_l_3677_, 0);
lean_inc(v_size_3708_);
v___y_3700_ = v_size_3708_;
goto v___jp_3699_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_unsigned_to_nat(0u);
v___y_3700_ = v___x_3709_;
goto v___jp_3699_;
}
v___jp_3687_:
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3691_ = lean_nat_add(v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec(v___y_3689_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 4, v_impl_3654_);
lean_ctor_set(v___x_3683_, 3, v_r_3678_);
lean_ctor_set(v___x_3683_, 2, v_v_3162_);
lean_ctor_set(v___x_3683_, 1, v_k_3161_);
lean_ctor_set(v___x_3683_, 0, v___x_3691_);
v___x_3693_ = v___x_3683_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_r_3678_);
lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_impl_3654_);
v___x_3693_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3695_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 4, v___x_3693_);
lean_ctor_set(v___x_3671_, 3, v___y_3688_);
lean_ctor_set(v___x_3671_, 2, v_v_3676_);
lean_ctor_set(v___x_3671_, 1, v_k_3675_);
lean_ctor_set(v___x_3671_, 0, v___x_3686_);
v___x_3695_ = v___x_3671_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_k_3675_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v_v_3676_);
lean_ctor_set(v_reuseFailAlloc_3696_, 3, v___y_3688_);
lean_ctor_set(v_reuseFailAlloc_3696_, 4, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
v___jp_3699_:
{
lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3701_ = lean_nat_add(v___x_3698_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec(v___x_3698_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_l_3677_);
lean_ctor_set(v___x_3166_, 3, v_l_3660_);
lean_ctor_set(v___x_3166_, 2, v_v_3659_);
lean_ctor_set(v___x_3166_, 1, v_k_3658_);
lean_ctor_set(v___x_3166_, 0, v___x_3701_);
v___x_3703_ = v___x_3166_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3701_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v_l_3660_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v_l_3677_);
v___x_3703_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3704_; 
v___x_3704_ = lean_nat_add(v___x_3655_, v_size_3656_);
lean_dec(v_size_3656_);
if (lean_obj_tag(v_r_3678_) == 0)
{
lean_object* v_size_3705_; 
v_size_3705_ = lean_ctor_get(v_r_3678_, 0);
lean_inc(v_size_3705_);
v___y_3688_ = v___x_3703_;
v___y_3689_ = v___x_3704_;
v___y_3690_ = v_size_3705_;
goto v___jp_3687_;
}
else
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_unsigned_to_nat(0u);
v___y_3688_ = v___x_3703_;
v___y_3689_ = v___x_3704_;
v___y_3690_ = v___x_3706_;
goto v___jp_3687_;
}
}
}
}
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_del_object(v___x_3166_);
v___x_3716_ = lean_nat_add(v___x_3655_, v_size_3657_);
lean_dec(v_size_3657_);
v___x_3717_ = lean_nat_add(v___x_3716_, v_size_3656_);
lean_dec(v___x_3716_);
v___x_3718_ = lean_nat_add(v___x_3655_, v_size_3656_);
lean_dec(v_size_3656_);
v___x_3719_ = lean_nat_add(v___x_3718_, v_size_3674_);
lean_dec(v___x_3718_);
lean_inc_ref(v_impl_3654_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 4, v_impl_3654_);
lean_ctor_set(v___x_3671_, 3, v_r_3661_);
lean_ctor_set(v___x_3671_, 2, v_v_3162_);
lean_ctor_set(v___x_3671_, 1, v_k_3161_);
lean_ctor_set(v___x_3671_, 0, v___x_3719_);
v___x_3721_ = v___x_3671_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_r_3661_);
lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_impl_3654_);
v___x_3721_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
v_isSharedCheck_3728_ = !lean_is_exclusive(v_impl_3654_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; 
v_unused_3729_ = lean_ctor_get(v_impl_3654_, 4);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_impl_3654_, 3);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_impl_3654_, 2);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_impl_3654_, 1);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_impl_3654_, 0);
lean_dec(v_unused_3733_);
v___x_3723_ = v_impl_3654_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_dec(v_impl_3654_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 4, v___x_3721_);
lean_ctor_set(v___x_3723_, 3, v_l_3660_);
lean_ctor_set(v___x_3723_, 2, v_v_3659_);
lean_ctor_set(v___x_3723_, 1, v_k_3658_);
lean_ctor_set(v___x_3723_, 0, v___x_3717_);
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_l_3660_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v___x_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3741_; lean_object* v___x_3742_; lean_object* v___x_3744_; 
v_size_3741_ = lean_ctor_get(v_impl_3654_, 0);
lean_inc(v_size_3741_);
v___x_3742_ = lean_nat_add(v___x_3655_, v_size_3741_);
lean_dec(v_size_3741_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_impl_3654_);
lean_ctor_set(v___x_3166_, 0, v___x_3742_);
v___x_3744_ = v___x_3166_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v_l_3163_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v_impl_3654_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
else
{
if (lean_obj_tag(v_l_3163_) == 0)
{
lean_object* v_l_3746_; 
v_l_3746_ = lean_ctor_get(v_l_3163_, 3);
if (lean_obj_tag(v_l_3746_) == 0)
{
lean_object* v_r_3747_; 
lean_inc_ref(v_l_3746_);
v_r_3747_ = lean_ctor_get(v_l_3163_, 4);
lean_inc(v_r_3747_);
if (lean_obj_tag(v_r_3747_) == 0)
{
lean_object* v_size_3748_; lean_object* v_k_3749_; lean_object* v_v_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3763_; 
v_size_3748_ = lean_ctor_get(v_l_3163_, 0);
v_k_3749_ = lean_ctor_get(v_l_3163_, 1);
v_v_3750_ = lean_ctor_get(v_l_3163_, 2);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_l_3163_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; lean_object* v_unused_3765_; 
v_unused_3764_ = lean_ctor_get(v_l_3163_, 4);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_l_3163_, 3);
lean_dec(v_unused_3765_);
v___x_3752_ = v_l_3163_;
v_isShared_3753_ = v_isSharedCheck_3763_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_v_3750_);
lean_inc(v_k_3749_);
lean_inc(v_size_3748_);
lean_dec(v_l_3163_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3763_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v_size_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
v_size_3754_ = lean_ctor_get(v_r_3747_, 0);
v___x_3755_ = lean_nat_add(v___x_3655_, v_size_3748_);
lean_dec(v_size_3748_);
v___x_3756_ = lean_nat_add(v___x_3655_, v_size_3754_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 4, v_impl_3654_);
lean_ctor_set(v___x_3752_, 3, v_r_3747_);
lean_ctor_set(v___x_3752_, 2, v_v_3162_);
lean_ctor_set(v___x_3752_, 1, v_k_3161_);
lean_ctor_set(v___x_3752_, 0, v___x_3756_);
v___x_3758_ = v___x_3752_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_r_3747_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_impl_3654_);
v___x_3758_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v___x_3758_);
lean_ctor_set(v___x_3166_, 3, v_l_3746_);
lean_ctor_set(v___x_3166_, 2, v_v_3750_);
lean_ctor_set(v___x_3166_, 1, v_k_3749_);
lean_ctor_set(v___x_3166_, 0, v___x_3755_);
v___x_3760_ = v___x_3166_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3749_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3750_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_l_3746_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
else
{
lean_object* v_k_3766_; lean_object* v_v_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3778_; 
v_k_3766_ = lean_ctor_get(v_l_3163_, 1);
v_v_3767_ = lean_ctor_get(v_l_3163_, 2);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_l_3163_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; lean_object* v_unused_3780_; lean_object* v_unused_3781_; 
v_unused_3779_ = lean_ctor_get(v_l_3163_, 4);
lean_dec(v_unused_3779_);
v_unused_3780_ = lean_ctor_get(v_l_3163_, 3);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v_l_3163_, 0);
lean_dec(v_unused_3781_);
v___x_3769_ = v_l_3163_;
v_isShared_3770_ = v_isSharedCheck_3778_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
lean_dec(v_l_3163_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3778_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3771_ = lean_unsigned_to_nat(3u);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 3, v_r_3747_);
lean_ctor_set(v___x_3769_, 2, v_v_3162_);
lean_ctor_set(v___x_3769_, 1, v_k_3161_);
lean_ctor_set(v___x_3769_, 0, v___x_3655_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3777_, 3, v_r_3747_);
lean_ctor_set(v_reuseFailAlloc_3777_, 4, v_r_3747_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v___x_3773_);
lean_ctor_set(v___x_3166_, 3, v_l_3746_);
lean_ctor_set(v___x_3166_, 2, v_v_3767_);
lean_ctor_set(v___x_3166_, 1, v_k_3766_);
lean_ctor_set(v___x_3166_, 0, v___x_3771_);
v___x_3775_ = v___x_3166_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_3776_, 3, v_l_3746_);
lean_ctor_set(v_reuseFailAlloc_3776_, 4, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
else
{
lean_object* v_r_3782_; 
v_r_3782_ = lean_ctor_get(v_l_3163_, 4);
lean_inc(v_r_3782_);
if (lean_obj_tag(v_r_3782_) == 0)
{
lean_object* v_k_3783_; lean_object* v_v_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3807_; 
lean_inc(v_l_3746_);
v_k_3783_ = lean_ctor_get(v_l_3163_, 1);
v_v_3784_ = lean_ctor_get(v_l_3163_, 2);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_l_3163_);
if (v_isSharedCheck_3807_ == 0)
{
lean_object* v_unused_3808_; lean_object* v_unused_3809_; lean_object* v_unused_3810_; 
v_unused_3808_ = lean_ctor_get(v_l_3163_, 4);
lean_dec(v_unused_3808_);
v_unused_3809_ = lean_ctor_get(v_l_3163_, 3);
lean_dec(v_unused_3809_);
v_unused_3810_ = lean_ctor_get(v_l_3163_, 0);
lean_dec(v_unused_3810_);
v___x_3786_ = v_l_3163_;
v_isShared_3787_ = v_isSharedCheck_3807_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_v_3784_);
lean_inc(v_k_3783_);
lean_dec(v_l_3163_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3807_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v_k_3788_; lean_object* v_v_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3803_; 
v_k_3788_ = lean_ctor_get(v_r_3782_, 1);
v_v_3789_ = lean_ctor_get(v_r_3782_, 2);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_r_3782_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; lean_object* v_unused_3805_; lean_object* v_unused_3806_; 
v_unused_3804_ = lean_ctor_get(v_r_3782_, 4);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_r_3782_, 3);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_r_3782_, 0);
lean_dec(v_unused_3806_);
v___x_3791_ = v_r_3782_;
v_isShared_3792_ = v_isSharedCheck_3803_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_v_3789_);
lean_inc(v_k_3788_);
lean_dec(v_r_3782_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3803_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
v___x_3793_ = lean_unsigned_to_nat(3u);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 4, v_l_3746_);
lean_ctor_set(v___x_3791_, 3, v_l_3746_);
lean_ctor_set(v___x_3791_, 2, v_v_3784_);
lean_ctor_set(v___x_3791_, 1, v_k_3783_);
lean_ctor_set(v___x_3791_, 0, v___x_3655_);
v___x_3795_ = v___x_3791_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_k_3783_);
lean_ctor_set(v_reuseFailAlloc_3802_, 2, v_v_3784_);
lean_ctor_set(v_reuseFailAlloc_3802_, 3, v_l_3746_);
lean_ctor_set(v_reuseFailAlloc_3802_, 4, v_l_3746_);
v___x_3795_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 4, v_l_3746_);
lean_ctor_set(v___x_3786_, 2, v_v_3162_);
lean_ctor_set(v___x_3786_, 1, v_k_3161_);
lean_ctor_set(v___x_3786_, 0, v___x_3655_);
v___x_3797_ = v___x_3786_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3801_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3801_, 3, v_l_3746_);
lean_ctor_set(v_reuseFailAlloc_3801_, 4, v_l_3746_);
v___x_3797_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3799_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v___x_3797_);
lean_ctor_set(v___x_3166_, 3, v___x_3795_);
lean_ctor_set(v___x_3166_, 2, v_v_3789_);
lean_ctor_set(v___x_3166_, 1, v_k_3788_);
lean_ctor_set(v___x_3166_, 0, v___x_3793_);
v___x_3799_ = v___x_3166_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_k_3788_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_v_3789_);
lean_ctor_set(v_reuseFailAlloc_3800_, 3, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3800_, 4, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = lean_unsigned_to_nat(2u);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_r_3782_);
lean_ctor_set(v___x_3166_, 0, v___x_3811_);
v___x_3813_ = v___x_3166_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3814_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3814_, 3, v_l_3163_);
lean_ctor_set(v_reuseFailAlloc_3814_, 4, v_r_3782_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v___x_3816_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v_l_3163_);
lean_ctor_set(v___x_3166_, 0, v___x_3655_);
v___x_3816_ = v___x_3166_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_k_3161_);
lean_ctor_set(v_reuseFailAlloc_3817_, 2, v_v_3162_);
lean_ctor_set(v_reuseFailAlloc_3817_, 3, v_l_3163_);
lean_ctor_set(v_reuseFailAlloc_3817_, 4, v_l_3163_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
}
}
else
{
return v_t_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3820_, lean_object* v_t_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3820_, v_t_3821_);
lean_dec(v_k_3820_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3823_, lean_object* v_x_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3823_, v_x_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3826_, lean_object* v_x_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3826_, v_x_3827_);
lean_dec(v_declName_3826_);
return v_res_3828_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; lean_object* v_env_3841_; lean_object* v___f_3842_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___x_3886_; 
v___x_3840_ = lean_st_ref_get(v___y_3838_);
v_env_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc_ref(v_env_3841_);
lean_dec(v___x_3840_);
lean_inc(v_declName_3832_);
v___f_3842_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3842_, 0, v_declName_3832_);
v___x_3886_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3841_, v_declName_3832_);
lean_dec_ref(v_env_3841_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_dec(v_declName_3832_);
v___y_3844_ = v___y_3836_;
v___y_3845_ = v___y_3838_;
goto v___jp_3843_;
}
else
{
uint8_t v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec_ref_known(v___x_3886_, 1);
lean_dec_ref(v___f_3842_);
v___x_3887_ = 0;
v___x_3888_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3889_ = l_Lean_MessageData_ofConstName(v_declName_3832_, v___x_3887_);
v___x_3890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3892_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
return v___x_3893_;
}
v___jp_3843_:
{
lean_object* v___x_3846_; lean_object* v_env_3847_; lean_object* v_nextMacroScope_3848_; lean_object* v_ngen_3849_; lean_object* v_auxDeclNGen_3850_; lean_object* v_traceState_3851_; lean_object* v_messages_3852_; lean_object* v_infoState_3853_; lean_object* v_snapshotTasks_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3884_; 
v___x_3846_ = lean_st_ref_take(v___y_3845_);
v_env_3847_ = lean_ctor_get(v___x_3846_, 0);
v_nextMacroScope_3848_ = lean_ctor_get(v___x_3846_, 1);
v_ngen_3849_ = lean_ctor_get(v___x_3846_, 2);
v_auxDeclNGen_3850_ = lean_ctor_get(v___x_3846_, 3);
v_traceState_3851_ = lean_ctor_get(v___x_3846_, 4);
v_messages_3852_ = lean_ctor_get(v___x_3846_, 6);
v_infoState_3853_ = lean_ctor_get(v___x_3846_, 7);
v_snapshotTasks_3854_ = lean_ctor_get(v___x_3846_, 8);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; 
v_unused_3885_ = lean_ctor_get(v___x_3846_, 5);
lean_dec(v_unused_3885_);
v___x_3856_ = v___x_3846_;
v_isShared_3857_ = v_isSharedCheck_3884_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_snapshotTasks_3854_);
lean_inc(v_infoState_3853_);
lean_inc(v_messages_3852_);
lean_inc(v_traceState_3851_);
lean_inc(v_auxDeclNGen_3850_);
lean_inc(v_ngen_3849_);
lean_inc(v_nextMacroScope_3848_);
lean_inc(v_env_3847_);
lean_dec(v___x_3846_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3884_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3864_; 
v___x_3858_ = l_Lean_docStringExt;
v___x_3859_ = lean_box(2);
v___x_3860_ = lean_box(0);
v___x_3861_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_3858_, v_env_3847_, v___f_3842_, v___x_3859_, v___x_3860_);
v___x_3862_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 5, v___x_3862_);
lean_ctor_set(v___x_3856_, 0, v___x_3861_);
v___x_3864_ = v___x_3856_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_nextMacroScope_3848_);
lean_ctor_set(v_reuseFailAlloc_3883_, 2, v_ngen_3849_);
lean_ctor_set(v_reuseFailAlloc_3883_, 3, v_auxDeclNGen_3850_);
lean_ctor_set(v_reuseFailAlloc_3883_, 4, v_traceState_3851_);
lean_ctor_set(v_reuseFailAlloc_3883_, 5, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3883_, 6, v_messages_3852_);
lean_ctor_set(v_reuseFailAlloc_3883_, 7, v_infoState_3853_);
lean_ctor_set(v_reuseFailAlloc_3883_, 8, v_snapshotTasks_3854_);
v___x_3864_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v_mctx_3867_; lean_object* v_zetaDeltaFVarIds_3868_; lean_object* v_postponed_3869_; lean_object* v_diag_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3881_; 
v___x_3865_ = lean_st_ref_put(v___y_3845_, v___x_3864_);
v___x_3866_ = lean_st_ref_take(v___y_3844_);
v_mctx_3867_ = lean_ctor_get(v___x_3866_, 0);
v_zetaDeltaFVarIds_3868_ = lean_ctor_get(v___x_3866_, 2);
v_postponed_3869_ = lean_ctor_get(v___x_3866_, 3);
v_diag_3870_ = lean_ctor_get(v___x_3866_, 4);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v___x_3866_, 1);
lean_dec(v_unused_3882_);
v___x_3872_ = v___x_3866_;
v_isShared_3873_ = v_isSharedCheck_3881_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_diag_3870_);
lean_inc(v_postponed_3869_);
lean_inc(v_zetaDeltaFVarIds_3868_);
lean_inc(v_mctx_3867_);
lean_dec(v___x_3866_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3881_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3874_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 1, v___x_3874_);
v___x_3876_ = v___x_3872_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_mctx_3867_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v_zetaDeltaFVarIds_3868_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v_postponed_3869_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v_diag_3870_);
v___x_3876_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3877_ = lean_st_ref_put(v___y_3844_, v___x_3876_);
v___x_3878_ = lean_box(0);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
return v___x_3879_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
return v_res_3902_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3905_ = l_Lean_stringToMessageData(v___x_3904_);
return v___x_3905_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3908_ = l_Lean_stringToMessageData(v___x_3907_);
return v___x_3908_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3911_ = l_Lean_stringToMessageData(v___x_3910_);
return v___x_3911_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3914_ = l_Lean_stringToMessageData(v___x_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_){
_start:
{
lean_object* v___x_3923_; lean_object* v_env_3924_; uint8_t v___x_3925_; lean_object* v___x_3926_; 
v___x_3923_ = lean_st_ref_get(v_a_3921_);
v_env_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc_ref(v_env_3924_);
lean_dec(v___x_3923_);
v___x_3925_ = 1;
lean_inc(v_declName_3915_);
v___x_3926_ = l_Lean_findInternalDocString_x3f(v_env_3924_, v_declName_3915_, v___x_3925_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v___x_3926_, 1);
if (lean_obj_tag(v_a_3927_) == 1)
{
lean_object* v_val_3928_; 
v_val_3928_ = lean_ctor_get(v_a_3927_, 0);
lean_inc(v_val_3928_);
lean_dec_ref_known(v_a_3927_, 1);
if (lean_obj_tag(v_val_3928_) == 0)
{
lean_object* v_val_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3951_; 
v_val_3929_ = lean_ctor_get(v_val_3928_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v_val_3928_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3931_ = v_val_3928_;
v_isShared_3932_ = v_isSharedCheck_3951_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_val_3929_);
lean_dec(v_val_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3951_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_removeBuiltinDocString(v_declName_3915_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v___x_3934_; 
lean_dec_ref_known(v___x_3933_, 1);
lean_del_object(v___x_3931_);
lean_inc(v_declName_3915_);
v___x_3934_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v___x_3935_; 
lean_dec_ref_known(v___x_3934_, 1);
v___x_3935_ = l_Lean_addVersoDocStringFromString(v_declName_3915_, v_val_3929_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
return v___x_3935_;
}
else
{
lean_dec(v_val_3929_);
lean_dec(v_declName_3915_);
return v___x_3934_;
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3950_; 
lean_dec(v_val_3929_);
lean_dec(v_declName_3915_);
v_a_3936_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3938_ = v___x_3933_;
v_isShared_3939_ = v_isSharedCheck_3950_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3933_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3950_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v_ref_3940_; lean_object* v___x_3941_; lean_object* v___x_3943_; 
v_ref_3940_ = lean_ctor_get(v_a_3920_, 2);
v___x_3941_ = lean_io_error_to_string(v_a_3936_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set_tag(v___x_3931_, 3);
lean_ctor_set(v___x_3931_, 0, v___x_3941_);
v___x_3943_ = v___x_3931_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3944_ = l_Lean_MessageData_ofFormat(v___x_3943_);
lean_inc(v_ref_3940_);
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v_ref_3940_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3945_);
v___x_3947_ = v___x_3938_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
}
else
{
lean_object* v___x_3952_; uint8_t v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
lean_dec(v_val_3928_);
v___x_3952_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3953_ = 0;
v___x_3954_ = l_Lean_MessageData_ofConstName(v_declName_3915_, v___x_3953_);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3952_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3957_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
return v___x_3958_;
}
}
else
{
lean_object* v___x_3959_; uint8_t v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_dec(v_a_3927_);
v___x_3959_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3960_ = 0;
v___x_3961_ = l_Lean_MessageData_ofConstName(v_declName_3915_, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3959_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3964_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
return v___x_3965_;
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3978_; 
lean_dec(v_declName_3915_);
v_a_3966_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3968_ = v___x_3926_;
v_isShared_3969_ = v_isSharedCheck_3978_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3926_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3978_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v_ref_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3976_; 
v_ref_3970_ = lean_ctor_get(v_a_3920_, 2);
v___x_3971_ = lean_io_error_to_string(v_a_3966_);
v___x_3972_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
v___x_3973_ = l_Lean_MessageData_ofFormat(v___x_3972_);
lean_inc(v_ref_3970_);
v___x_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3974_, 0, v_ref_3970_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3974_);
v___x_3976_ = v___x_3968_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_makeDocStringVerso(v_declName_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3988_, lean_object* v_k_3989_, lean_object* v_t_3990_, lean_object* v_h_3991_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3989_, v_t_3990_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3993_, lean_object* v_k_3994_, lean_object* v_t_3995_, lean_object* v_h_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3993_, v_k_3994_, v_t_3995_, v_h_3996_);
lean_dec(v_k_3994_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3998_, lean_object* v_binders_3999_, lean_object* v_docComment_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
uint8_t v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = l_Lean_isVersoDocComment(v_docComment_4000_);
v___x_4009_ = l_Lean_addDocStringOf(v___x_4008_, v_declName_3998_, v_binders_3999_, v_docComment_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_4010_, lean_object* v_binders_4011_, lean_object* v_docComment_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_addDocString(v_declName_4010_, v_binders_4011_, v_docComment_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_4021_, lean_object* v_binders_4022_, lean_object* v_docString_x3f_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_){
_start:
{
if (lean_obj_tag(v_docString_x3f_4023_) == 0)
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
lean_dec(v_binders_4022_);
lean_dec(v_declName_4021_);
v___x_4031_ = lean_box(0);
v___x_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
else
{
lean_object* v_val_4033_; lean_object* v___x_4034_; 
v_val_4033_ = lean_ctor_get(v_docString_x3f_4023_, 0);
lean_inc(v_val_4033_);
lean_dec_ref_known(v_docString_x3f_4023_, 1);
v___x_4034_ = l_Lean_addDocString(v_declName_4021_, v_binders_4022_, v_val_4033_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_);
return v___x_4034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_4035_, lean_object* v_binders_4036_, lean_object* v_docString_x3f_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_addDocString_x27(v_declName_4035_, v_binders_4036_, v_docString_x3f_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___x_4050_; lean_object* v_nextMacroScope_4051_; lean_object* v_ngen_4052_; lean_object* v_auxDeclNGen_4053_; lean_object* v_traceState_4054_; lean_object* v_messages_4055_; lean_object* v_infoState_4056_; lean_object* v_snapshotTasks_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4083_; 
v___x_4050_ = lean_st_ref_take(v___y_4048_);
v_nextMacroScope_4051_ = lean_ctor_get(v___x_4050_, 1);
v_ngen_4052_ = lean_ctor_get(v___x_4050_, 2);
v_auxDeclNGen_4053_ = lean_ctor_get(v___x_4050_, 3);
v_traceState_4054_ = lean_ctor_get(v___x_4050_, 4);
v_messages_4055_ = lean_ctor_get(v___x_4050_, 6);
v_infoState_4056_ = lean_ctor_get(v___x_4050_, 7);
v_snapshotTasks_4057_ = lean_ctor_get(v___x_4050_, 8);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; lean_object* v_unused_4085_; 
v_unused_4084_ = lean_ctor_get(v___x_4050_, 5);
lean_dec(v_unused_4084_);
v_unused_4085_ = lean_ctor_get(v___x_4050_, 0);
lean_dec(v_unused_4085_);
v___x_4059_ = v___x_4050_;
v_isShared_4060_ = v_isSharedCheck_4083_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_snapshotTasks_4057_);
lean_inc(v_infoState_4056_);
lean_inc(v_messages_4055_);
lean_inc(v_traceState_4054_);
lean_inc(v_auxDeclNGen_4053_);
lean_inc(v_ngen_4052_);
lean_inc(v_nextMacroScope_4051_);
lean_dec(v___x_4050_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4083_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4061_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 5, v___x_4061_);
lean_ctor_set(v___x_4059_, 0, v_env_4046_);
v___x_4063_ = v___x_4059_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_env_4046_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_nextMacroScope_4051_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_ngen_4052_);
lean_ctor_set(v_reuseFailAlloc_4082_, 3, v_auxDeclNGen_4053_);
lean_ctor_set(v_reuseFailAlloc_4082_, 4, v_traceState_4054_);
lean_ctor_set(v_reuseFailAlloc_4082_, 5, v___x_4061_);
lean_ctor_set(v_reuseFailAlloc_4082_, 6, v_messages_4055_);
lean_ctor_set(v_reuseFailAlloc_4082_, 7, v_infoState_4056_);
lean_ctor_set(v_reuseFailAlloc_4082_, 8, v_snapshotTasks_4057_);
v___x_4063_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v_mctx_4066_; lean_object* v_zetaDeltaFVarIds_4067_; lean_object* v_postponed_4068_; lean_object* v_diag_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4080_; 
v___x_4064_ = lean_st_ref_put(v___y_4048_, v___x_4063_);
v___x_4065_ = lean_st_ref_take(v___y_4047_);
v_mctx_4066_ = lean_ctor_get(v___x_4065_, 0);
v_zetaDeltaFVarIds_4067_ = lean_ctor_get(v___x_4065_, 2);
v_postponed_4068_ = lean_ctor_get(v___x_4065_, 3);
v_diag_4069_ = lean_ctor_get(v___x_4065_, 4);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; 
v_unused_4081_ = lean_ctor_get(v___x_4065_, 1);
lean_dec(v_unused_4081_);
v___x_4071_ = v___x_4065_;
v_isShared_4072_ = v_isSharedCheck_4080_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_diag_4069_);
lean_inc(v_postponed_4068_);
lean_inc(v_zetaDeltaFVarIds_4067_);
lean_inc(v_mctx_4066_);
lean_dec(v___x_4065_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4080_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4073_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 1, v___x_4073_);
v___x_4075_ = v___x_4071_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_mctx_4066_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_zetaDeltaFVarIds_4067_);
lean_ctor_set(v_reuseFailAlloc_4079_, 3, v_postponed_4068_);
lean_ctor_set(v_reuseFailAlloc_4079_, 4, v_diag_4069_);
v___x_4075_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = lean_st_ref_put(v___y_4047_, v___x_4075_);
v___x_4077_ = lean_box(0);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
return v___x_4078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec(v___y_4087_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_4091_, lean_object* v_as_4092_, size_t v_i_4093_, size_t v_stop_4094_, lean_object* v_b_4095_){
_start:
{
uint8_t v___x_4096_; 
v___x_4096_ = lean_usize_dec_eq(v_i_4093_, v_stop_4094_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v_index_4098_; lean_object* v_sourceString_4099_; lean_object* v_imports_4100_; lean_object* v_currNamespace_4101_; lean_object* v_openDecls_4102_; lean_object* v_options_4103_; lean_object* v_check_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4120_; 
v___x_4097_ = lean_array_uget(v_as_4092_, v_i_4093_);
v_index_4098_ = lean_ctor_get(v___x_4097_, 1);
v_sourceString_4099_ = lean_ctor_get(v___x_4097_, 2);
v_imports_4100_ = lean_ctor_get(v___x_4097_, 3);
v_currNamespace_4101_ = lean_ctor_get(v___x_4097_, 4);
v_openDecls_4102_ = lean_ctor_get(v___x_4097_, 5);
v_options_4103_ = lean_ctor_get(v___x_4097_, 6);
v_check_4104_ = lean_ctor_get(v___x_4097_, 7);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4120_ == 0)
{
lean_object* v_unused_4121_; 
v_unused_4121_ = lean_ctor_get(v___x_4097_, 0);
lean_dec(v_unused_4121_);
v___x_4106_ = v___x_4097_;
v_isShared_4107_ = v_isSharedCheck_4120_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_check_4104_);
lean_inc(v_options_4103_);
lean_inc(v_openDecls_4102_);
lean_inc(v_currNamespace_4101_);
lean_inc(v_imports_4100_);
lean_inc(v_sourceString_4099_);
lean_inc(v_index_4098_);
lean_dec(v___x_4097_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4120_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v_toEnvExtension_4109_; lean_object* v_asyncMode_4110_; lean_object* v___x_4111_; lean_object* v___x_4113_; 
v___x_4108_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_4109_ = lean_ctor_get(v___x_4108_, 0);
v_asyncMode_4110_ = lean_ctor_get(v_toEnvExtension_4109_, 2);
lean_inc(v_n_4091_);
v___x_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4111_, 0, v_n_4091_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4111_);
v___x_4113_ = v___x_4106_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v_index_4098_);
lean_ctor_set(v_reuseFailAlloc_4119_, 2, v_sourceString_4099_);
lean_ctor_set(v_reuseFailAlloc_4119_, 3, v_imports_4100_);
lean_ctor_set(v_reuseFailAlloc_4119_, 4, v_currNamespace_4101_);
lean_ctor_set(v_reuseFailAlloc_4119_, 5, v_openDecls_4102_);
lean_ctor_set(v_reuseFailAlloc_4119_, 6, v_options_4103_);
lean_ctor_set(v_reuseFailAlloc_4119_, 7, v_check_4104_);
v___x_4113_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; size_t v___x_4116_; size_t v___x_4117_; 
v___x_4114_ = lean_box(0);
v___x_4115_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4108_, v_b_4095_, v___x_4113_, v_asyncMode_4110_, v___x_4114_);
v___x_4116_ = ((size_t)1ULL);
v___x_4117_ = lean_usize_add(v_i_4093_, v___x_4116_);
v_i_4093_ = v___x_4117_;
v_b_4095_ = v___x_4115_;
goto _start;
}
}
}
else
{
lean_dec(v_n_4091_);
return v_b_4095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_4122_, lean_object* v_as_4123_, lean_object* v_i_4124_, lean_object* v_stop_4125_, lean_object* v_b_4126_){
_start:
{
size_t v_i_boxed_4127_; size_t v_stop_boxed_4128_; lean_object* v_res_4129_; 
v_i_boxed_4127_ = lean_unbox_usize(v_i_4124_);
lean_dec(v_i_4124_);
v_stop_boxed_4128_ = lean_unbox_usize(v_stop_4125_);
lean_dec(v_stop_4125_);
v_res_4129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_4122_, v_as_4123_, v_i_boxed_4127_, v_stop_boxed_4128_, v_b_4126_);
lean_dec_ref(v_as_4123_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4130_, lean_object* v_deferred_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___x_4139_; lean_object* v_env_4140_; lean_object* v___x_4141_; uint8_t v___x_4142_; 
v___x_4139_ = lean_st_ref_get(v___y_4137_);
v_env_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc_ref(v_env_4140_);
lean_dec(v___x_4139_);
v___x_4141_ = l_Lean_getMainModuleDoc(v_env_4140_);
v___x_4142_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4141_);
lean_dec_ref(v___x_4141_);
if (v___x_4142_ == 0)
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_dec_ref(v_docs_4130_);
v___x_4143_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_4144_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4143_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4144_;
}
else
{
lean_object* v___x_4145_; lean_object* v_env_4146_; lean_object* v___x_4147_; lean_object* v_size_4148_; lean_object* v___x_4149_; lean_object* v_env_4150_; lean_object* v___x_4151_; 
v___x_4145_ = lean_st_ref_get(v___y_4137_);
v_env_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc_ref(v_env_4146_);
lean_dec(v___x_4145_);
v___x_4147_ = l_Lean_getMainVersoModuleDocs(v_env_4146_);
v_size_4148_ = lean_ctor_get(v___x_4147_, 2);
lean_inc(v_size_4148_);
lean_dec_ref(v___x_4147_);
v___x_4149_ = lean_st_ref_get(v___y_4137_);
v_env_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc_ref(v_env_4150_);
lean_dec(v___x_4149_);
v___x_4151_ = l_Lean_addVersoModuleDocSnippet(v_env_4150_, v_docs_4130_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_dec(v_size_4148_);
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4154_ = l_Lean_stringToMessageData(v_a_4152_);
v___x_4155_ = l_Lean_indentD(v___x_4154_);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4153_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4156_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4157_;
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v_a_4158_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = lean_array_get_size(v_deferred_4131_);
v___x_4161_ = lean_nat_dec_lt(v___x_4159_, v___x_4160_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; 
lean_dec(v_size_4148_);
v___x_4162_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4158_, v___y_4135_, v___y_4137_);
return v___x_4162_;
}
else
{
size_t v___x_4163_; size_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4163_ = ((size_t)0ULL);
v___x_4164_ = lean_usize_of_nat(v___x_4160_);
v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4148_, v_deferred_4131_, v___x_4163_, v___x_4164_, v_a_4158_);
v___x_4166_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4165_, v___y_4135_, v___y_4137_);
return v___x_4166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4167_, lean_object* v_deferred_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4167_, v_deferred_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec_ref(v_deferred_4168_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4177_, lean_object* v_doc_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_versoModDocString(v_range_4177_, v_doc_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v_fst_4188_; lean_object* v_snd_4189_; lean_object* v___x_4190_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
v_fst_4188_ = lean_ctor_get(v_a_4187_, 0);
lean_inc(v_fst_4188_);
v_snd_4189_ = lean_ctor_get(v_a_4187_, 1);
lean_inc(v_snd_4189_);
lean_dec(v_a_4187_);
v___x_4190_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_4188_, v_snd_4189_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec(v_snd_4189_);
return v___x_4190_;
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
v_a_4191_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4186_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4186_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4199_, lean_object* v_doc_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_addVersoModDocString(v_range_4199_, v_doc_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
lean_dec(v_a_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_a_4204_);
lean_dec_ref(v_a_4203_);
lean_dec(v_a_4202_);
lean_dec_ref(v_a_4201_);
lean_dec(v_doc_4200_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4209_, v___y_4213_, v___y_4215_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
return v_res_4226_;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_DeferredCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
lean_object* initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_DeferredCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Add(builtin);
}
#ifdef __cplusplus
}
#endif

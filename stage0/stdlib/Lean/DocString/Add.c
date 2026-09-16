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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Doc_Parser_BlockCtxt_forDocString(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabModSnippet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object*);
lean_object* l_Lean_getMainModuleDoc(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_versoDocStringExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Doc_parseFailureKind;
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
uint8_t l_Lean_isVersoDocComment(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "The "};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1;
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = " of this documentation comment has no source location, so it cannot be parsed."};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation(lean_object*);
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "closing delimiter"};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2;
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5;
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "opening delimiter"};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "This documentation comment has an unexpected structure, so it cannot be parsed."};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringOfText___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_versoDocString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_versoDocString___closed__0 = (const lean_object*)&l_Lean_versoDocString___closed__0_value;
static const lean_string_object l_Lean_versoDocString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_versoDocString___closed__1 = (const lean_object*)&l_Lean_versoDocString___closed__1_value;
static const lean_string_object l_Lean_versoDocString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_versoDocString___closed__2 = (const lean_object*)&l_Lean_versoDocString___closed__2_value;
static const lean_string_object l_Lean_versoDocString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_versoDocString___closed__3 = (const lean_object*)&l_Lean_versoDocString___closed__3_value;
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_0),((lean_object*)&l_Lean_versoDocString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_1),((lean_object*)&l_Lean_versoDocString___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_2),((lean_object*)&l_Lean_versoDocString___closed__3_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l_Lean_versoDocString___closed__4 = (const lean_object*)&l_Lean_versoDocString___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx(lean_object* v_x_189_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(0u);
return v___x_190_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_unsigned_to_nat(1u);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx___boxed(lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_VersoDocstringMarkup_ctorIdx(v_x_192_);
lean_dec_ref(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___redArg(lean_object* v_t_194_, lean_object* v_k_195_){
_start:
{
lean_object* v_doc_196_; lean_object* v___x_197_; 
v_doc_196_ = lean_ctor_get(v_t_194_, 0);
lean_inc(v_doc_196_);
lean_dec_ref(v_t_194_);
v___x_197_ = lean_apply_1(v_k_195_, v_doc_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim(lean_object* v_motive_198_, lean_object* v_ctorIdx_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_k_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_200_, v_k_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___boxed(lean_object* v_motive_204_, lean_object* v_ctorIdx_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_k_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_VersoDocstringMarkup_ctorElim(v_motive_204_, v_ctorIdx_205_, v_t_206_, v_h_207_, v_k_208_);
lean_dec(v_ctorIdx_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim___redArg(lean_object* v_t_210_, lean_object* v_document_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_210_, v_document_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_document_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_214_, v_document_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim___redArg(lean_object* v_t_218_, lean_object* v_parseFailure_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_218_, v_parseFailure_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim(lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_parseFailure_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_222_, v_parseFailure_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx(lean_object* v_x_226_){
_start:
{
lean_object* v_doc_227_; 
v_doc_227_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_doc_227_);
return v_doc_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx___boxed(lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_VersoDocstringMarkup_stx(v_x_228_);
lean_dec_ref(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of(lean_object* v_docComment_230_){
_start:
{
lean_object* v___x_231_; lean_object* v_body_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___y_236_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v_body_232_ = l_Lean_Syntax_getArg(v_docComment_230_, v___x_231_);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = l_Lean_Syntax_getArg(v_docComment_230_, v___x_233_);
v___x_239_ = l_Lean_Syntax_getArg(v_body_232_, v___x_233_);
v___x_240_ = l_Lean_Doc_parseFailureKind;
lean_inc(v___x_239_);
v___x_241_ = l_Lean_Syntax_isOfKind(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
v___y_236_ = v___x_242_;
goto v___jp_235_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = l_Lean_Syntax_getArg(v___x_239_, v___x_233_);
lean_dec(v___x_239_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
v___y_236_ = v___x_244_;
goto v___jp_235_;
}
v___jp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = l_Lean_Syntax_getArg(v_body_232_, v___x_231_);
lean_dec(v_body_232_);
v___x_238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_234_);
lean_ctor_set(v___x_238_, 1, v___y_236_);
lean_ctor_set(v___x_238_, 2, v___x_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of___boxed(lean_object* v_docComment_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_VersoDocstringView_of(v_docComment_245_);
lean_dec(v_docComment_245_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2));
v___x_252_ = l_Lean_stringToMessageData(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation(lean_object* v_what_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_254_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1, &l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1);
v___x_255_ = l_Lean_stringToMessageData(v_what_253_);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3, &l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3_once, _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0));
v___x_261_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3));
v___x_266_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6));
v___x_271_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange(lean_object* v_view_274_){
_start:
{
lean_object* v_opener_275_; lean_object* v_markup_276_; lean_object* v_closer_277_; uint8_t v___x_278_; lean_object* v___x_279_; 
v_opener_275_ = lean_ctor_get(v_view_274_, 0);
v_markup_276_ = lean_ctor_get(v_view_274_, 1);
v_closer_277_ = lean_ctor_get(v_view_274_, 2);
v___x_278_ = 1;
v___x_279_ = l_Lean_Syntax_getPos_x3f(v_opener_275_, v___x_278_);
if (lean_obj_tag(v___x_279_) == 1)
{
lean_object* v_val_280_; lean_object* v___y_282_; lean_object* v_doc_298_; 
v_val_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v___x_279_, 1);
v_doc_298_ = lean_ctor_get(v_markup_276_, 0);
v___y_282_ = v_doc_298_;
goto v___jp_281_;
v___jp_281_:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Syntax_getPos_x3f(v___y_282_, v___x_278_);
if (lean_obj_tag(v___x_283_) == 1)
{
lean_object* v_val_284_; lean_object* v___x_285_; 
v_val_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v___x_283_, 1);
v___x_285_ = l_Lean_Syntax_getPos_x3f(v_closer_277_, v___x_278_);
if (lean_obj_tag(v___x_285_) == 1)
{
lean_object* v_val_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_295_; 
v_val_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_295_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_val_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_val_284_);
lean_ctor_set(v___x_290_, 1, v_val_286_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_val_280_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_291_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v___x_296_; 
lean_dec(v___x_285_);
lean_dec(v_val_284_);
lean_dec(v_val_280_);
v___x_296_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2);
return v___x_296_;
}
}
else
{
lean_object* v___x_297_; 
lean_dec(v___x_283_);
lean_dec(v_val_280_);
v___x_297_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5);
return v___x_297_;
}
}
}
else
{
lean_object* v___x_299_; 
lean_dec(v___x_279_);
v___x_299_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___boxed(lean_object* v_view_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_300_);
lean_dec_ref(v_view_300_);
return v_res_301_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1, &l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange(lean_object* v_docComment_307_){
_start:
{
if (lean_obj_tag(v_docComment_307_) == 1)
{
lean_object* v_args_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_args_310_ = lean_ctor_get(v_docComment_307_, 2);
v___x_311_ = lean_array_get_size(v_args_310_);
v___x_312_ = lean_unsigned_to_nat(2u);
v___x_313_ = lean_nat_dec_eq(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
goto v___jp_308_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_array_fget_borrowed(v_args_310_, v___x_314_);
if (lean_obj_tag(v___x_315_) == 1)
{
lean_object* v_args_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_args_316_ = lean_ctor_get(v___x_315_, 2);
v___x_317_ = lean_array_get_size(v_args_316_);
v___x_318_ = lean_nat_dec_eq(v___x_317_, v___x_312_);
if (v___x_318_ == 0)
{
goto v___jp_308_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_array_fget_borrowed(v_args_310_, v___x_319_);
v___x_321_ = l_Lean_Syntax_getPos_x3f(v___x_320_, v___x_318_);
if (lean_obj_tag(v___x_321_) == 1)
{
lean_object* v_val_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_val_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_array_fget_borrowed(v_args_316_, v___x_319_);
v___x_324_ = l_Lean_Syntax_getPos_x3f(v___x_323_, v___x_318_);
if (lean_obj_tag(v___x_324_) == 1)
{
lean_object* v_val_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_val_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = lean_array_fget_borrowed(v_args_316_, v___x_314_);
v___x_327_ = l_Lean_Syntax_getPos_x3f(v___x_326_, v___x_318_);
if (lean_obj_tag(v___x_327_) == 1)
{
lean_object* v_val_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_337_; 
v_val_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_337_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_337_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_val_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_337_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_val_325_);
lean_ctor_set(v___x_332_, 1, v_val_328_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_val_322_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_333_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
lean_object* v___x_338_; 
lean_dec(v___x_327_);
lean_dec(v_val_325_);
lean_dec(v_val_322_);
v___x_338_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2);
return v___x_338_;
}
}
else
{
lean_object* v___x_339_; 
lean_dec(v___x_324_);
lean_dec(v_val_322_);
v___x_339_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5);
return v___x_339_;
}
}
else
{
lean_object* v___x_340_; 
lean_dec(v___x_321_);
v___x_340_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8);
return v___x_340_;
}
}
}
else
{
goto v___jp_308_;
}
}
}
else
{
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___boxed(lean_object* v_docComment_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_341_);
lean_dec(v_docComment_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object* v_toPure_343_, lean_object* v_____r_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_box(0);
v___x_346_ = lean_apply_2(v_toPure_343_, lean_box(0), v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object* v_toPure_347_, lean_object* v_____s_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_box(0);
v___x_350_ = lean_apply_2(v_toPure_347_, lean_box(0), v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object* v___x_351_, lean_object* v_toPure_352_, lean_object* v_____r_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_351_);
v___x_355_ = lean_apply_2(v_toPure_352_, lean_box(0), v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object* v_ictx_356_, lean_object* v_logMessage_357_, lean_object* v_toBind_358_, lean_object* v___f_359_, lean_object* v_a_360_, lean_object* v_x_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_snd_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_snd_363_ = lean_ctor_get(v_a_360_, 1);
lean_inc(v_snd_363_);
v_fst_364_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_fst_364_);
lean_dec_ref(v_a_360_);
v_snd_365_ = lean_ctor_get(v_snd_363_, 1);
lean_inc(v_snd_365_);
lean_dec(v_snd_363_);
v___x_366_ = l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(v_ictx_356_, v_fst_364_, v_snd_365_);
v___x_367_ = lean_apply_1(v_logMessage_357_, v___x_366_);
v___x_368_ = lean_apply_4(v_toBind_358_, lean_box(0), lean_box(0), v___x_367_, v___f_359_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object* v_text_371_, lean_object* v_pos_372_, lean_object* v_source_373_, uint8_t v___x_374_, lean_object* v_logMessage_375_, lean_object* v_toBind_376_, lean_object* v___f_377_, lean_object* v_____do__lift_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint32_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_379_ = l_Lean_FileMap_toPosition(v_text_371_, v_pos_372_);
v___x_380_ = lean_box(0);
v___x_381_ = 2;
v___x_382_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_383_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__0));
v___x_384_ = lean_string_utf8_get(v_source_373_, v_pos_372_);
v___x_385_ = lean_string_push(v___x_382_, v___x_384_);
v___x_386_ = lean_string_append(v___x_383_, v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__1));
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
v___x_389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
v___x_390_ = l_Lean_MessageData_ofFormat(v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_391_, 0, v_____do__lift_378_);
lean_ctor_set(v___x_391_, 1, v___x_379_);
lean_ctor_set(v___x_391_, 2, v___x_380_);
lean_ctor_set(v___x_391_, 3, v___x_382_);
lean_ctor_set(v___x_391_, 4, v___x_390_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*5, v___x_374_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*5 + 1, v___x_381_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*5 + 2, v___x_374_);
v___x_392_ = lean_apply_1(v_logMessage_375_, v___x_391_);
v___x_393_ = lean_apply_4(v_toBind_376_, lean_box(0), lean_box(0), v___x_392_, v___f_377_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object* v_text_394_, lean_object* v_pos_395_, lean_object* v_source_396_, lean_object* v___x_397_, lean_object* v_logMessage_398_, lean_object* v_toBind_399_, lean_object* v___f_400_, lean_object* v_____do__lift_401_){
_start:
{
uint8_t v___x_877__boxed_402_; lean_object* v_res_403_; 
v___x_877__boxed_402_ = lean_unbox(v___x_397_);
v_res_403_ = l_Lean_parseVersoDocString___redArg___lam__4(v_text_394_, v_pos_395_, v_source_396_, v___x_877__boxed_402_, v_logMessage_398_, v_toBind_399_, v___f_400_, v_____do__lift_401_);
lean_dec_ref(v_source_396_);
lean_dec(v_pos_395_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object* v_env_404_, lean_object* v_____do__lift_405_, lean_object* v_____do__lift_406_, lean_object* v_text_407_, lean_object* v_fst_408_, lean_object* v_fst_409_, lean_object* v___y_410_, lean_object* v_source_411_, lean_object* v_ictx_412_, lean_object* v_toPure_413_, lean_object* v_logMessage_414_, lean_object* v_toBind_415_, lean_object* v_inst_416_, lean_object* v___f_417_, lean_object* v___f_418_, lean_object* v_getFileName_419_, lean_object* v_____do__lift_420_){
_start:
{
lean_object* v_pmctx_421_; lean_object* v_blockCtxt_422_; lean_object* v___x_423_; lean_object* v_s_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_s_427_; lean_object* v_errors_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
lean_inc_ref(v_env_404_);
v_pmctx_421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_421_, 0, v_env_404_);
lean_ctor_set(v_pmctx_421_, 1, v_____do__lift_405_);
lean_ctor_set(v_pmctx_421_, 2, v_____do__lift_406_);
lean_ctor_set(v_pmctx_421_, 3, v_____do__lift_420_);
lean_inc(v_fst_409_);
lean_inc_ref(v_text_407_);
v_blockCtxt_422_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_407_, v_fst_408_, v_fst_409_, v___y_410_);
v___x_423_ = l_Lean_Parser_mkParserState(v_source_411_);
v_s_424_ = l_Lean_Parser_ParserState_setPos(v___x_423_, v_fst_409_);
lean_inc_ref(v_blockCtxt_422_);
v___x_425_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_425_, 0, v_blockCtxt_422_);
v___x_426_ = l_Lean_Parser_getTokenTable(v_env_404_);
lean_inc_ref(v___x_426_);
lean_inc_ref(v_pmctx_421_);
lean_inc_ref_n(v_ictx_412_, 2);
v_s_427_ = l_Lean_Parser_ParserFn_run(v___x_425_, v_ictx_412_, v_pmctx_421_, v___x_426_, v_s_424_);
lean_inc_ref(v_s_427_);
v_errors_428_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v_ictx_412_, v_pmctx_421_, v___x_426_, v_source_411_, v_blockCtxt_422_, v_s_427_);
v___x_429_ = lean_array_get_size(v_errors_428_);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_nat_dec_eq(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___f_433_; lean_object* v___f_434_; size_t v_sz_435_; size_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec_ref(v_s_427_);
lean_dec(v_getFileName_419_);
lean_dec(v___f_418_);
lean_dec_ref(v_source_411_);
lean_dec_ref(v_text_407_);
v___x_432_ = lean_box(0);
v___f_433_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_433_, 0, v___x_432_);
lean_closure_set(v___f_433_, 1, v_toPure_413_);
lean_inc(v_toBind_415_);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3), 7, 4);
lean_closure_set(v___f_434_, 0, v_ictx_412_);
lean_closure_set(v___f_434_, 1, v_logMessage_414_);
lean_closure_set(v___f_434_, 2, v_toBind_415_);
lean_closure_set(v___f_434_, 3, v___f_433_);
v_sz_435_ = lean_array_size(v_errors_428_);
v___x_436_ = ((size_t)0ULL);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_416_, v_errors_428_, v___f_434_, v_sz_435_, v___x_436_, v___x_432_);
v___x_438_ = lean_apply_4(v_toBind_415_, lean_box(0), lean_box(0), v___x_437_, v___f_417_);
return v___x_438_;
}
else
{
lean_object* v_stxStack_439_; lean_object* v_pos_440_; uint8_t v___x_441_; 
lean_dec_ref(v_errors_428_);
lean_dec(v___f_417_);
lean_dec_ref(v_inst_416_);
v_stxStack_439_ = lean_ctor_get(v_s_427_, 0);
lean_inc_ref(v_stxStack_439_);
v_pos_440_ = lean_ctor_get(v_s_427_, 2);
lean_inc(v_pos_440_);
lean_dec_ref(v_s_427_);
v___x_441_ = l_Lean_Parser_InputContext_atEnd(v_ictx_412_, v_pos_440_);
lean_dec_ref(v_ictx_412_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___f_443_; lean_object* v___x_444_; 
lean_dec_ref(v_stxStack_439_);
lean_dec(v_toPure_413_);
v___x_442_ = lean_box(v___x_441_);
lean_inc(v_toBind_415_);
v___f_443_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_443_, 0, v_text_407_);
lean_closure_set(v___f_443_, 1, v_pos_440_);
lean_closure_set(v___f_443_, 2, v_source_411_);
lean_closure_set(v___f_443_, 3, v___x_442_);
lean_closure_set(v___f_443_, 4, v_logMessage_414_);
lean_closure_set(v___f_443_, 5, v_toBind_415_);
lean_closure_set(v___f_443_, 6, v___f_418_);
v___x_444_ = lean_apply_4(v_toBind_415_, lean_box(0), lean_box(0), v_getFileName_419_, v___f_443_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_pos_440_);
lean_dec(v_getFileName_419_);
lean_dec(v___f_418_);
lean_dec(v_toBind_415_);
lean_dec(v_logMessage_414_);
lean_dec_ref(v_source_411_);
lean_dec_ref(v_text_407_);
v___x_445_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_439_);
lean_dec_ref(v_stxStack_439_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
v___x_447_ = lean_apply_2(v_toPure_413_, lean_box(0), v___x_446_);
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_env_448_ = _args[0];
lean_object* v_____do__lift_449_ = _args[1];
lean_object* v_____do__lift_450_ = _args[2];
lean_object* v_text_451_ = _args[3];
lean_object* v_fst_452_ = _args[4];
lean_object* v_fst_453_ = _args[5];
lean_object* v___y_454_ = _args[6];
lean_object* v_source_455_ = _args[7];
lean_object* v_ictx_456_ = _args[8];
lean_object* v_toPure_457_ = _args[9];
lean_object* v_logMessage_458_ = _args[10];
lean_object* v_toBind_459_ = _args[11];
lean_object* v_inst_460_ = _args[12];
lean_object* v___f_461_ = _args[13];
lean_object* v___f_462_ = _args[14];
lean_object* v_getFileName_463_ = _args[15];
lean_object* v_____do__lift_464_ = _args[16];
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_parseVersoDocString___redArg___lam__5(v_env_448_, v_____do__lift_449_, v_____do__lift_450_, v_text_451_, v_fst_452_, v_fst_453_, v___y_454_, v_source_455_, v_ictx_456_, v_toPure_457_, v_logMessage_458_, v_toBind_459_, v_inst_460_, v___f_461_, v___f_462_, v_getFileName_463_, v_____do__lift_464_);
lean_dec(v_fst_452_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object* v_env_466_, lean_object* v_____do__lift_467_, lean_object* v_text_468_, lean_object* v_fst_469_, lean_object* v_fst_470_, lean_object* v___y_471_, lean_object* v_source_472_, lean_object* v_ictx_473_, lean_object* v_toPure_474_, lean_object* v_logMessage_475_, lean_object* v_toBind_476_, lean_object* v_inst_477_, lean_object* v___f_478_, lean_object* v___f_479_, lean_object* v_getFileName_480_, lean_object* v_getOpenDecls_481_, lean_object* v_____do__lift_482_){
_start:
{
lean_object* v___f_483_; lean_object* v___x_484_; 
lean_inc(v_toBind_476_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_483_, 0, v_env_466_);
lean_closure_set(v___f_483_, 1, v_____do__lift_467_);
lean_closure_set(v___f_483_, 2, v_____do__lift_482_);
lean_closure_set(v___f_483_, 3, v_text_468_);
lean_closure_set(v___f_483_, 4, v_fst_469_);
lean_closure_set(v___f_483_, 5, v_fst_470_);
lean_closure_set(v___f_483_, 6, v___y_471_);
lean_closure_set(v___f_483_, 7, v_source_472_);
lean_closure_set(v___f_483_, 8, v_ictx_473_);
lean_closure_set(v___f_483_, 9, v_toPure_474_);
lean_closure_set(v___f_483_, 10, v_logMessage_475_);
lean_closure_set(v___f_483_, 11, v_toBind_476_);
lean_closure_set(v___f_483_, 12, v_inst_477_);
lean_closure_set(v___f_483_, 13, v___f_478_);
lean_closure_set(v___f_483_, 14, v___f_479_);
lean_closure_set(v___f_483_, 15, v_getFileName_480_);
v___x_484_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v_getOpenDecls_481_, v___f_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_env_485_ = _args[0];
lean_object* v_____do__lift_486_ = _args[1];
lean_object* v_text_487_ = _args[2];
lean_object* v_fst_488_ = _args[3];
lean_object* v_fst_489_ = _args[4];
lean_object* v___y_490_ = _args[5];
lean_object* v_source_491_ = _args[6];
lean_object* v_ictx_492_ = _args[7];
lean_object* v_toPure_493_ = _args[8];
lean_object* v_logMessage_494_ = _args[9];
lean_object* v_toBind_495_ = _args[10];
lean_object* v_inst_496_ = _args[11];
lean_object* v___f_497_ = _args[12];
lean_object* v___f_498_ = _args[13];
lean_object* v_getFileName_499_ = _args[14];
lean_object* v_getOpenDecls_500_ = _args[15];
lean_object* v_____do__lift_501_ = _args[16];
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_parseVersoDocString___redArg___lam__6(v_env_485_, v_____do__lift_486_, v_text_487_, v_fst_488_, v_fst_489_, v___y_490_, v_source_491_, v_ictx_492_, v_toPure_493_, v_logMessage_494_, v_toBind_495_, v_inst_496_, v___f_497_, v___f_498_, v_getFileName_499_, v_getOpenDecls_500_, v_____do__lift_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object* v_inst_503_, lean_object* v_env_504_, lean_object* v_text_505_, lean_object* v_fst_506_, lean_object* v_fst_507_, lean_object* v___y_508_, lean_object* v_source_509_, lean_object* v_ictx_510_, lean_object* v_toPure_511_, lean_object* v_logMessage_512_, lean_object* v_toBind_513_, lean_object* v_inst_514_, lean_object* v___f_515_, lean_object* v___f_516_, lean_object* v_getFileName_517_, lean_object* v_____do__lift_518_){
_start:
{
lean_object* v_getCurrNamespace_519_; lean_object* v_getOpenDecls_520_; lean_object* v___f_521_; lean_object* v___x_522_; 
v_getCurrNamespace_519_ = lean_ctor_get(v_inst_503_, 0);
lean_inc(v_getCurrNamespace_519_);
v_getOpenDecls_520_ = lean_ctor_get(v_inst_503_, 1);
lean_inc(v_getOpenDecls_520_);
lean_dec_ref(v_inst_503_);
lean_inc(v_toBind_513_);
v___f_521_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__6___boxed), 17, 16);
lean_closure_set(v___f_521_, 0, v_env_504_);
lean_closure_set(v___f_521_, 1, v_____do__lift_518_);
lean_closure_set(v___f_521_, 2, v_text_505_);
lean_closure_set(v___f_521_, 3, v_fst_506_);
lean_closure_set(v___f_521_, 4, v_fst_507_);
lean_closure_set(v___f_521_, 5, v___y_508_);
lean_closure_set(v___f_521_, 6, v_source_509_);
lean_closure_set(v___f_521_, 7, v_ictx_510_);
lean_closure_set(v___f_521_, 8, v_toPure_511_);
lean_closure_set(v___f_521_, 9, v_logMessage_512_);
lean_closure_set(v___f_521_, 10, v_toBind_513_);
lean_closure_set(v___f_521_, 11, v_inst_514_);
lean_closure_set(v___f_521_, 12, v___f_515_);
lean_closure_set(v___f_521_, 13, v___f_516_);
lean_closure_set(v___f_521_, 14, v_getFileName_517_);
lean_closure_set(v___f_521_, 15, v_getOpenDecls_520_);
v___x_522_ = lean_apply_4(v_toBind_513_, lean_box(0), lean_box(0), v_getCurrNamespace_519_, v___f_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object* v_source_523_, lean_object* v_text_524_, lean_object* v___y_525_, lean_object* v_inst_526_, lean_object* v_env_527_, lean_object* v_fst_528_, lean_object* v_fst_529_, lean_object* v_toPure_530_, lean_object* v_logMessage_531_, lean_object* v_toBind_532_, lean_object* v_inst_533_, lean_object* v___f_534_, lean_object* v___f_535_, lean_object* v_getFileName_536_, lean_object* v_inst_537_, lean_object* v_____do__lift_538_){
_start:
{
lean_object* v_ictx_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
lean_inc(v___y_525_);
lean_inc_ref(v_text_524_);
lean_inc_ref(v_source_523_);
v_ictx_539_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_539_, 0, v_source_523_);
lean_ctor_set(v_ictx_539_, 1, v_____do__lift_538_);
lean_ctor_set(v_ictx_539_, 2, v_text_524_);
lean_ctor_set(v_ictx_539_, 3, v___y_525_);
lean_inc(v_toBind_532_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__7), 16, 15);
lean_closure_set(v___f_540_, 0, v_inst_526_);
lean_closure_set(v___f_540_, 1, v_env_527_);
lean_closure_set(v___f_540_, 2, v_text_524_);
lean_closure_set(v___f_540_, 3, v_fst_528_);
lean_closure_set(v___f_540_, 4, v_fst_529_);
lean_closure_set(v___f_540_, 5, v___y_525_);
lean_closure_set(v___f_540_, 6, v_source_523_);
lean_closure_set(v___f_540_, 7, v_ictx_539_);
lean_closure_set(v___f_540_, 8, v_toPure_530_);
lean_closure_set(v___f_540_, 9, v_logMessage_531_);
lean_closure_set(v___f_540_, 10, v_toBind_532_);
lean_closure_set(v___f_540_, 11, v_inst_533_);
lean_closure_set(v___f_540_, 12, v___f_534_);
lean_closure_set(v___f_540_, 13, v___f_535_);
lean_closure_set(v___f_540_, 14, v_getFileName_536_);
v___x_541_ = lean_apply_4(v_toBind_532_, lean_box(0), lean_box(0), v_inst_537_, v___f_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object* v_inst_542_, lean_object* v_source_543_, lean_object* v_text_544_, lean_object* v___y_545_, lean_object* v_inst_546_, lean_object* v_fst_547_, lean_object* v_fst_548_, lean_object* v_toPure_549_, lean_object* v_toBind_550_, lean_object* v_inst_551_, lean_object* v___f_552_, lean_object* v___f_553_, lean_object* v_inst_554_, lean_object* v_env_555_){
_start:
{
lean_object* v_getFileName_556_; lean_object* v_logMessage_557_; lean_object* v___f_558_; lean_object* v___x_559_; 
v_getFileName_556_ = lean_ctor_get(v_inst_542_, 2);
lean_inc_n(v_getFileName_556_, 2);
v_logMessage_557_ = lean_ctor_get(v_inst_542_, 4);
lean_inc(v_logMessage_557_);
lean_dec_ref(v_inst_542_);
lean_inc(v_toBind_550_);
v___f_558_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__8), 16, 15);
lean_closure_set(v___f_558_, 0, v_source_543_);
lean_closure_set(v___f_558_, 1, v_text_544_);
lean_closure_set(v___f_558_, 2, v___y_545_);
lean_closure_set(v___f_558_, 3, v_inst_546_);
lean_closure_set(v___f_558_, 4, v_env_555_);
lean_closure_set(v___f_558_, 5, v_fst_547_);
lean_closure_set(v___f_558_, 6, v_fst_548_);
lean_closure_set(v___f_558_, 7, v_toPure_549_);
lean_closure_set(v___f_558_, 8, v_logMessage_557_);
lean_closure_set(v___f_558_, 9, v_toBind_550_);
lean_closure_set(v___f_558_, 10, v_inst_551_);
lean_closure_set(v___f_558_, 11, v___f_552_);
lean_closure_set(v___f_558_, 12, v___f_553_);
lean_closure_set(v___f_558_, 13, v_getFileName_556_);
lean_closure_set(v___f_558_, 14, v_inst_554_);
v___x_559_ = lean_apply_4(v_toBind_550_, lean_box(0), lean_box(0), v_getFileName_556_, v___f_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object* v_text_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_toPure_564_, lean_object* v_toBind_565_, lean_object* v_inst_566_, lean_object* v___f_567_, lean_object* v___f_568_, lean_object* v_inst_569_, lean_object* v_____x_570_){
_start:
{
lean_object* v_snd_571_; lean_object* v_fst_572_; lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v_source_575_; lean_object* v___y_577_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_snd_571_ = lean_ctor_get(v_____x_570_, 1);
lean_inc(v_snd_571_);
v_fst_572_ = lean_ctor_get(v_____x_570_, 0);
lean_inc(v_fst_572_);
lean_dec_ref(v_____x_570_);
v_fst_573_ = lean_ctor_get(v_snd_571_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v_snd_571_, 1);
lean_inc(v_snd_574_);
lean_dec(v_snd_571_);
v_source_575_ = lean_ctor_get(v_text_560_, 0);
lean_inc_ref(v_source_575_);
v___x_581_ = lean_string_utf8_byte_size(v_source_575_);
v___x_582_ = lean_nat_dec_le(v_snd_574_, v___x_581_);
if (v___x_582_ == 0)
{
lean_dec(v_snd_574_);
v___y_577_ = v___x_581_;
goto v___jp_576_;
}
else
{
v___y_577_ = v_snd_574_;
goto v___jp_576_;
}
v___jp_576_:
{
lean_object* v_getEnv_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v_getEnv_578_ = lean_ctor_get(v_inst_561_, 0);
lean_inc(v_getEnv_578_);
lean_dec_ref(v_inst_561_);
lean_inc(v_toBind_565_);
v___f_579_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__9), 14, 13);
lean_closure_set(v___f_579_, 0, v_inst_562_);
lean_closure_set(v___f_579_, 1, v_source_575_);
lean_closure_set(v___f_579_, 2, v_text_560_);
lean_closure_set(v___f_579_, 3, v___y_577_);
lean_closure_set(v___f_579_, 4, v_inst_563_);
lean_closure_set(v___f_579_, 5, v_fst_572_);
lean_closure_set(v___f_579_, 6, v_fst_573_);
lean_closure_set(v___f_579_, 7, v_toPure_564_);
lean_closure_set(v___f_579_, 8, v_toBind_565_);
lean_closure_set(v___f_579_, 9, v_inst_566_);
lean_closure_set(v___f_579_, 10, v___f_567_);
lean_closure_set(v___f_579_, 11, v___f_568_);
lean_closure_set(v___f_579_, 12, v_inst_569_);
v___x_580_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v_getEnv_578_, v___f_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object* v___f_583_, lean_object* v_____x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_apply_1(v___f_583_, v_____x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__13(lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_toPure_589_, lean_object* v_toBind_590_, lean_object* v_inst_591_, lean_object* v___f_592_, lean_object* v___f_593_, lean_object* v_inst_594_, lean_object* v_docComment_595_, lean_object* v_inst_596_, lean_object* v_text_597_){
_start:
{
lean_object* v___f_598_; lean_object* v___x_599_; 
lean_inc_ref(v_inst_591_);
lean_inc(v_toBind_590_);
lean_inc(v_toPure_589_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__10), 11, 10);
lean_closure_set(v___f_598_, 0, v_text_597_);
lean_closure_set(v___f_598_, 1, v_inst_586_);
lean_closure_set(v___f_598_, 2, v_inst_587_);
lean_closure_set(v___f_598_, 3, v_inst_588_);
lean_closure_set(v___f_598_, 4, v_toPure_589_);
lean_closure_set(v___f_598_, 5, v_toBind_590_);
lean_closure_set(v___f_598_, 6, v_inst_591_);
lean_closure_set(v___f_598_, 7, v___f_592_);
lean_closure_set(v___f_598_, 8, v___f_593_);
lean_closure_set(v___f_598_, 9, v_inst_594_);
v___x_599_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_595_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_toPure_589_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 2, 1);
lean_closure_set(v___f_601_, 0, v___f_598_);
v___x_602_ = l_Lean_throwError___redArg(v_inst_591_, v_inst_596_, v_a_600_);
v___x_603_ = lean_apply_4(v_toBind_590_, lean_box(0), lean_box(0), v___x_602_, v___f_601_);
return v___x_603_;
}
else
{
lean_object* v_a_604_; lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec_ref(v_inst_596_);
lean_dec_ref(v_inst_591_);
v_a_604_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_599_, 1);
v___f_605_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 2, 1);
lean_closure_set(v___f_605_, 0, v___f_598_);
v___x_606_ = lean_apply_2(v_toPure_589_, lean_box(0), v_a_604_);
v___x_607_ = lean_apply_4(v_toBind_590_, lean_box(0), lean_box(0), v___x_606_, v___f_605_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__13___boxed(lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_toPure_611_, lean_object* v_toBind_612_, lean_object* v_inst_613_, lean_object* v___f_614_, lean_object* v___f_615_, lean_object* v_inst_616_, lean_object* v_docComment_617_, lean_object* v_inst_618_, lean_object* v_text_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_parseVersoDocString___redArg___lam__13(v_inst_608_, v_inst_609_, v_inst_610_, v_toPure_611_, v_toBind_612_, v_inst_613_, v___f_614_, v___f_615_, v_inst_616_, v_docComment_617_, v_inst_618_, v_text_619_);
lean_dec(v_docComment_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_docComment_628_){
_start:
{
lean_object* v_toApplicative_629_; lean_object* v_toBind_630_; lean_object* v_toPure_631_; lean_object* v___f_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___x_635_; 
v_toApplicative_629_ = lean_ctor_get(v_inst_621_, 0);
v_toBind_630_ = lean_ctor_get(v_inst_621_, 1);
lean_inc_n(v_toBind_630_, 2);
v_toPure_631_ = lean_ctor_get(v_toApplicative_629_, 1);
lean_inc_n(v_toPure_631_, 3);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__0), 2, 1);
lean_closure_set(v___f_632_, 0, v_toPure_631_);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__1), 2, 1);
lean_closure_set(v___f_633_, 0, v_toPure_631_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__13___boxed), 12, 11);
lean_closure_set(v___f_634_, 0, v_inst_624_);
lean_closure_set(v___f_634_, 1, v_inst_626_);
lean_closure_set(v___f_634_, 2, v_inst_627_);
lean_closure_set(v___f_634_, 3, v_toPure_631_);
lean_closure_set(v___f_634_, 4, v_toBind_630_);
lean_closure_set(v___f_634_, 5, v_inst_621_);
lean_closure_set(v___f_634_, 6, v___f_633_);
lean_closure_set(v___f_634_, 7, v___f_632_);
lean_closure_set(v___f_634_, 8, v_inst_625_);
lean_closure_set(v___f_634_, 9, v_docComment_628_);
lean_closure_set(v___f_634_, 10, v_inst_623_);
v___x_635_ = lean_apply_4(v_toBind_630_, lean_box(0), lean_box(0), v_inst_622_, v___f_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_m_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_docComment_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_parseVersoDocString___redArg(v_inst_637_, v_inst_638_, v_inst_639_, v_inst_640_, v_inst_641_, v_inst_642_, v_inst_643_, v_docComment_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object* v_text_646_, lean_object* v_pos_647_, lean_object* v_source_648_, uint8_t v___x_649_, lean_object* v_logMessage_650_, lean_object* v_____do__lift_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint32_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_652_ = l_Lean_FileMap_toPosition(v_text_646_, v_pos_647_);
v___x_653_ = lean_box(0);
v___x_654_ = 2;
v___x_655_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_656_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__0));
v___x_657_ = lean_string_utf8_get(v_source_648_, v_pos_647_);
v___x_658_ = lean_string_push(v___x_655_, v___x_657_);
v___x_659_ = lean_string_append(v___x_656_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_660_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__1));
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
v___x_662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
v___x_663_ = l_Lean_MessageData_ofFormat(v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_664_, 0, v_____do__lift_651_);
lean_ctor_set(v___x_664_, 1, v___x_652_);
lean_ctor_set(v___x_664_, 2, v___x_653_);
lean_ctor_set(v___x_664_, 3, v___x_655_);
lean_ctor_set(v___x_664_, 4, v___x_663_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*5, v___x_649_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*5 + 1, v___x_654_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*5 + 2, v___x_649_);
v___x_665_ = lean_apply_1(v_logMessage_650_, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object* v_text_666_, lean_object* v_pos_667_, lean_object* v_source_668_, lean_object* v___x_669_, lean_object* v_logMessage_670_, lean_object* v_____do__lift_671_){
_start:
{
uint8_t v___x_627__boxed_672_; lean_object* v_res_673_; 
v___x_627__boxed_672_ = lean_unbox(v___x_669_);
v_res_673_ = l_Lean_reportVersoParseFailure___redArg___lam__0(v_text_666_, v_pos_667_, v_source_668_, v___x_627__boxed_672_, v_logMessage_670_, v_____do__lift_671_);
lean_dec_ref(v_source_668_);
lean_dec(v_pos_667_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object* v_toPure_674_, lean_object* v_errors_675_, lean_object* v_s_676_, lean_object* v_ictx_677_, lean_object* v_text_678_, lean_object* v_source_679_, lean_object* v_logMessage_680_, lean_object* v_toBind_681_, lean_object* v_getFileName_682_, lean_object* v_____s_683_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = lean_array_get_size(v_errors_675_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_nat_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_dec(v_getFileName_682_);
lean_dec(v_toBind_681_);
lean_dec(v_logMessage_680_);
lean_dec_ref(v_source_679_);
lean_dec_ref(v_text_678_);
lean_dec_ref(v_s_676_);
goto v___jp_684_;
}
else
{
lean_object* v_pos_690_; uint8_t v___x_691_; 
v_pos_690_ = lean_ctor_get(v_s_676_, 2);
lean_inc(v_pos_690_);
lean_dec_ref(v_s_676_);
v___x_691_ = l_Lean_Parser_InputContext_atEnd(v_ictx_677_, v_pos_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___f_693_; lean_object* v___x_694_; 
lean_dec(v_toPure_674_);
v___x_692_ = lean_box(v___x_691_);
v___f_693_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_693_, 0, v_text_678_);
lean_closure_set(v___f_693_, 1, v_pos_690_);
lean_closure_set(v___f_693_, 2, v_source_679_);
lean_closure_set(v___f_693_, 3, v___x_692_);
lean_closure_set(v___f_693_, 4, v_logMessage_680_);
v___x_694_ = lean_apply_4(v_toBind_681_, lean_box(0), lean_box(0), v_getFileName_682_, v___f_693_);
return v___x_694_;
}
else
{
lean_dec(v_pos_690_);
lean_dec(v_getFileName_682_);
lean_dec(v_toBind_681_);
lean_dec(v_logMessage_680_);
lean_dec_ref(v_source_679_);
lean_dec_ref(v_text_678_);
goto v___jp_684_;
}
}
v___jp_684_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_box(0);
v___x_686_ = lean_apply_2(v_toPure_674_, lean_box(0), v___x_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object* v_toPure_695_, lean_object* v_errors_696_, lean_object* v_s_697_, lean_object* v_ictx_698_, lean_object* v_text_699_, lean_object* v_source_700_, lean_object* v_logMessage_701_, lean_object* v_toBind_702_, lean_object* v_getFileName_703_, lean_object* v_____s_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_reportVersoParseFailure___redArg___lam__1(v_toPure_695_, v_errors_696_, v_s_697_, v_ictx_698_, v_text_699_, v_source_700_, v_logMessage_701_, v_toBind_702_, v_getFileName_703_, v_____s_704_);
lean_dec_ref(v_ictx_698_);
lean_dec_ref(v_errors_696_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object* v_env_706_, lean_object* v_____do__lift_707_, lean_object* v_____do__lift_708_, lean_object* v_text_709_, lean_object* v_fst_710_, lean_object* v_fst_711_, lean_object* v___y_712_, lean_object* v_source_713_, lean_object* v_ictx_714_, lean_object* v_toPure_715_, lean_object* v_logMessage_716_, lean_object* v_toBind_717_, lean_object* v_getFileName_718_, lean_object* v_inst_719_, lean_object* v_____do__lift_720_){
_start:
{
lean_object* v_pmctx_721_; lean_object* v_blockCtxt_722_; lean_object* v___x_723_; lean_object* v_s_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_s_727_; lean_object* v_errors_728_; lean_object* v___f_729_; lean_object* v___x_730_; lean_object* v___f_731_; lean_object* v___f_732_; size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc_ref(v_env_706_);
v_pmctx_721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_721_, 0, v_env_706_);
lean_ctor_set(v_pmctx_721_, 1, v_____do__lift_707_);
lean_ctor_set(v_pmctx_721_, 2, v_____do__lift_708_);
lean_ctor_set(v_pmctx_721_, 3, v_____do__lift_720_);
lean_inc(v_fst_711_);
lean_inc_ref(v_text_709_);
v_blockCtxt_722_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_709_, v_fst_710_, v_fst_711_, v___y_712_);
v___x_723_ = l_Lean_Parser_mkParserState(v_source_713_);
v_s_724_ = l_Lean_Parser_ParserState_setPos(v___x_723_, v_fst_711_);
lean_inc_ref(v_blockCtxt_722_);
v___x_725_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_725_, 0, v_blockCtxt_722_);
v___x_726_ = l_Lean_Parser_getTokenTable(v_env_706_);
lean_inc_ref(v___x_726_);
lean_inc_ref(v_pmctx_721_);
lean_inc_ref_n(v_ictx_714_, 3);
v_s_727_ = l_Lean_Parser_ParserFn_run(v___x_725_, v_ictx_714_, v_pmctx_721_, v___x_726_, v_s_724_);
lean_inc_ref(v_s_727_);
v_errors_728_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v_ictx_714_, v_pmctx_721_, v___x_726_, v_source_713_, v_blockCtxt_722_, v_s_727_);
lean_inc_n(v_toBind_717_, 2);
lean_inc(v_logMessage_716_);
lean_inc_ref(v_errors_728_);
lean_inc(v_toPure_715_);
v___f_729_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_729_, 0, v_toPure_715_);
lean_closure_set(v___f_729_, 1, v_errors_728_);
lean_closure_set(v___f_729_, 2, v_s_727_);
lean_closure_set(v___f_729_, 3, v_ictx_714_);
lean_closure_set(v___f_729_, 4, v_text_709_);
lean_closure_set(v___f_729_, 5, v_source_713_);
lean_closure_set(v___f_729_, 6, v_logMessage_716_);
lean_closure_set(v___f_729_, 7, v_toBind_717_);
lean_closure_set(v___f_729_, 8, v_getFileName_718_);
v___x_730_ = lean_box(0);
v___f_731_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_731_, 0, v___x_730_);
lean_closure_set(v___f_731_, 1, v_toPure_715_);
v___f_732_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3), 7, 4);
lean_closure_set(v___f_732_, 0, v_ictx_714_);
lean_closure_set(v___f_732_, 1, v_logMessage_716_);
lean_closure_set(v___f_732_, 2, v_toBind_717_);
lean_closure_set(v___f_732_, 3, v___f_731_);
v_sz_733_ = lean_array_size(v_errors_728_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_719_, v_errors_728_, v___f_732_, v_sz_733_, v___x_734_, v___x_730_);
v___x_736_ = lean_apply_4(v_toBind_717_, lean_box(0), lean_box(0), v___x_735_, v___f_729_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4___boxed(lean_object* v_env_737_, lean_object* v_____do__lift_738_, lean_object* v_____do__lift_739_, lean_object* v_text_740_, lean_object* v_fst_741_, lean_object* v_fst_742_, lean_object* v___y_743_, lean_object* v_source_744_, lean_object* v_ictx_745_, lean_object* v_toPure_746_, lean_object* v_logMessage_747_, lean_object* v_toBind_748_, lean_object* v_getFileName_749_, lean_object* v_inst_750_, lean_object* v_____do__lift_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_reportVersoParseFailure___redArg___lam__4(v_env_737_, v_____do__lift_738_, v_____do__lift_739_, v_text_740_, v_fst_741_, v_fst_742_, v___y_743_, v_source_744_, v_ictx_745_, v_toPure_746_, v_logMessage_747_, v_toBind_748_, v_getFileName_749_, v_inst_750_, v_____do__lift_751_);
lean_dec(v_fst_741_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object* v_env_753_, lean_object* v_____do__lift_754_, lean_object* v_text_755_, lean_object* v_fst_756_, lean_object* v_fst_757_, lean_object* v___y_758_, lean_object* v_source_759_, lean_object* v_ictx_760_, lean_object* v_toPure_761_, lean_object* v_logMessage_762_, lean_object* v_toBind_763_, lean_object* v_getFileName_764_, lean_object* v_inst_765_, lean_object* v_getOpenDecls_766_, lean_object* v_____do__lift_767_){
_start:
{
lean_object* v___f_768_; lean_object* v___x_769_; 
lean_inc(v_toBind_763_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_768_, 0, v_env_753_);
lean_closure_set(v___f_768_, 1, v_____do__lift_754_);
lean_closure_set(v___f_768_, 2, v_____do__lift_767_);
lean_closure_set(v___f_768_, 3, v_text_755_);
lean_closure_set(v___f_768_, 4, v_fst_756_);
lean_closure_set(v___f_768_, 5, v_fst_757_);
lean_closure_set(v___f_768_, 6, v___y_758_);
lean_closure_set(v___f_768_, 7, v_source_759_);
lean_closure_set(v___f_768_, 8, v_ictx_760_);
lean_closure_set(v___f_768_, 9, v_toPure_761_);
lean_closure_set(v___f_768_, 10, v_logMessage_762_);
lean_closure_set(v___f_768_, 11, v_toBind_763_);
lean_closure_set(v___f_768_, 12, v_getFileName_764_);
lean_closure_set(v___f_768_, 13, v_inst_765_);
v___x_769_ = lean_apply_4(v_toBind_763_, lean_box(0), lean_box(0), v_getOpenDecls_766_, v___f_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object* v_inst_770_, lean_object* v_env_771_, lean_object* v_text_772_, lean_object* v_fst_773_, lean_object* v_fst_774_, lean_object* v___y_775_, lean_object* v_source_776_, lean_object* v_ictx_777_, lean_object* v_toPure_778_, lean_object* v_logMessage_779_, lean_object* v_toBind_780_, lean_object* v_getFileName_781_, lean_object* v_inst_782_, lean_object* v_____do__lift_783_){
_start:
{
lean_object* v_getCurrNamespace_784_; lean_object* v_getOpenDecls_785_; lean_object* v___f_786_; lean_object* v___x_787_; 
v_getCurrNamespace_784_ = lean_ctor_get(v_inst_770_, 0);
lean_inc(v_getCurrNamespace_784_);
v_getOpenDecls_785_ = lean_ctor_get(v_inst_770_, 1);
lean_inc(v_getOpenDecls_785_);
lean_dec_ref(v_inst_770_);
lean_inc(v_toBind_780_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__2), 15, 14);
lean_closure_set(v___f_786_, 0, v_env_771_);
lean_closure_set(v___f_786_, 1, v_____do__lift_783_);
lean_closure_set(v___f_786_, 2, v_text_772_);
lean_closure_set(v___f_786_, 3, v_fst_773_);
lean_closure_set(v___f_786_, 4, v_fst_774_);
lean_closure_set(v___f_786_, 5, v___y_775_);
lean_closure_set(v___f_786_, 6, v_source_776_);
lean_closure_set(v___f_786_, 7, v_ictx_777_);
lean_closure_set(v___f_786_, 8, v_toPure_778_);
lean_closure_set(v___f_786_, 9, v_logMessage_779_);
lean_closure_set(v___f_786_, 10, v_toBind_780_);
lean_closure_set(v___f_786_, 11, v_getFileName_781_);
lean_closure_set(v___f_786_, 12, v_inst_782_);
lean_closure_set(v___f_786_, 13, v_getOpenDecls_785_);
v___x_787_ = lean_apply_4(v_toBind_780_, lean_box(0), lean_box(0), v_getCurrNamespace_784_, v___f_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object* v_source_788_, lean_object* v_text_789_, lean_object* v___y_790_, lean_object* v_inst_791_, lean_object* v_env_792_, lean_object* v_fst_793_, lean_object* v_fst_794_, lean_object* v_toPure_795_, lean_object* v_logMessage_796_, lean_object* v_toBind_797_, lean_object* v_getFileName_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_____do__lift_801_){
_start:
{
lean_object* v_ictx_802_; lean_object* v___f_803_; lean_object* v___x_804_; 
lean_inc(v___y_790_);
lean_inc_ref(v_text_789_);
lean_inc_ref(v_source_788_);
v_ictx_802_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_802_, 0, v_source_788_);
lean_ctor_set(v_ictx_802_, 1, v_____do__lift_801_);
lean_ctor_set(v_ictx_802_, 2, v_text_789_);
lean_ctor_set(v_ictx_802_, 3, v___y_790_);
lean_inc(v_toBind_797_);
v___f_803_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__3), 14, 13);
lean_closure_set(v___f_803_, 0, v_inst_791_);
lean_closure_set(v___f_803_, 1, v_env_792_);
lean_closure_set(v___f_803_, 2, v_text_789_);
lean_closure_set(v___f_803_, 3, v_fst_793_);
lean_closure_set(v___f_803_, 4, v_fst_794_);
lean_closure_set(v___f_803_, 5, v___y_790_);
lean_closure_set(v___f_803_, 6, v_source_788_);
lean_closure_set(v___f_803_, 7, v_ictx_802_);
lean_closure_set(v___f_803_, 8, v_toPure_795_);
lean_closure_set(v___f_803_, 9, v_logMessage_796_);
lean_closure_set(v___f_803_, 10, v_toBind_797_);
lean_closure_set(v___f_803_, 11, v_getFileName_798_);
lean_closure_set(v___f_803_, 12, v_inst_799_);
v___x_804_ = lean_apply_4(v_toBind_797_, lean_box(0), lean_box(0), v_inst_800_, v___f_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object* v_inst_805_, lean_object* v_source_806_, lean_object* v_text_807_, lean_object* v___y_808_, lean_object* v_inst_809_, lean_object* v_fst_810_, lean_object* v_fst_811_, lean_object* v_toPure_812_, lean_object* v_toBind_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_env_816_){
_start:
{
lean_object* v_getFileName_817_; lean_object* v_logMessage_818_; lean_object* v___f_819_; lean_object* v___x_820_; 
v_getFileName_817_ = lean_ctor_get(v_inst_805_, 2);
lean_inc_n(v_getFileName_817_, 2);
v_logMessage_818_ = lean_ctor_get(v_inst_805_, 4);
lean_inc(v_logMessage_818_);
lean_dec_ref(v_inst_805_);
lean_inc(v_toBind_813_);
v___f_819_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__5), 14, 13);
lean_closure_set(v___f_819_, 0, v_source_806_);
lean_closure_set(v___f_819_, 1, v_text_807_);
lean_closure_set(v___f_819_, 2, v___y_808_);
lean_closure_set(v___f_819_, 3, v_inst_809_);
lean_closure_set(v___f_819_, 4, v_env_816_);
lean_closure_set(v___f_819_, 5, v_fst_810_);
lean_closure_set(v___f_819_, 6, v_fst_811_);
lean_closure_set(v___f_819_, 7, v_toPure_812_);
lean_closure_set(v___f_819_, 8, v_logMessage_818_);
lean_closure_set(v___f_819_, 9, v_toBind_813_);
lean_closure_set(v___f_819_, 10, v_getFileName_817_);
lean_closure_set(v___f_819_, 11, v_inst_814_);
lean_closure_set(v___f_819_, 12, v_inst_815_);
v___x_820_ = lean_apply_4(v_toBind_813_, lean_box(0), lean_box(0), v_getFileName_817_, v___f_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_fst_824_, lean_object* v_fst_825_, lean_object* v_toPure_826_, lean_object* v_toBind_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_snd_830_, lean_object* v_text_831_){
_start:
{
lean_object* v_source_832_; lean_object* v___y_834_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_source_832_ = lean_ctor_get(v_text_831_, 0);
lean_inc_ref(v_source_832_);
v___x_838_ = lean_string_utf8_byte_size(v_source_832_);
v___x_839_ = lean_nat_dec_le(v_snd_830_, v___x_838_);
if (v___x_839_ == 0)
{
lean_dec(v_snd_830_);
v___y_834_ = v___x_838_;
goto v___jp_833_;
}
else
{
v___y_834_ = v_snd_830_;
goto v___jp_833_;
}
v___jp_833_:
{
lean_object* v_getEnv_835_; lean_object* v___f_836_; lean_object* v___x_837_; 
v_getEnv_835_ = lean_ctor_get(v_inst_821_, 0);
lean_inc(v_getEnv_835_);
lean_dec_ref(v_inst_821_);
lean_inc(v_toBind_827_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__6), 12, 11);
lean_closure_set(v___f_836_, 0, v_inst_822_);
lean_closure_set(v___f_836_, 1, v_source_832_);
lean_closure_set(v___f_836_, 2, v_text_831_);
lean_closure_set(v___f_836_, 3, v___y_834_);
lean_closure_set(v___f_836_, 4, v_inst_823_);
lean_closure_set(v___f_836_, 5, v_fst_824_);
lean_closure_set(v___f_836_, 6, v_fst_825_);
lean_closure_set(v___f_836_, 7, v_toPure_826_);
lean_closure_set(v___f_836_, 8, v_toBind_827_);
lean_closure_set(v___f_836_, 9, v_inst_828_);
lean_closure_set(v___f_836_, 10, v_inst_829_);
v___x_837_ = lean_apply_4(v_toBind_827_, lean_box(0), lean_box(0), v_getEnv_835_, v___f_836_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_toPure_843_, lean_object* v_toBind_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_____x_848_){
_start:
{
lean_object* v_snd_849_; lean_object* v_fst_850_; lean_object* v_fst_851_; lean_object* v_snd_852_; lean_object* v___f_853_; lean_object* v___x_854_; 
v_snd_849_ = lean_ctor_get(v_____x_848_, 1);
lean_inc(v_snd_849_);
v_fst_850_ = lean_ctor_get(v_____x_848_, 0);
lean_inc(v_fst_850_);
lean_dec_ref(v_____x_848_);
v_fst_851_ = lean_ctor_get(v_snd_849_, 0);
lean_inc(v_fst_851_);
v_snd_852_ = lean_ctor_get(v_snd_849_, 1);
lean_inc(v_snd_852_);
lean_dec(v_snd_849_);
lean_inc(v_toBind_844_);
v___f_853_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__7), 11, 10);
lean_closure_set(v___f_853_, 0, v_inst_840_);
lean_closure_set(v___f_853_, 1, v_inst_841_);
lean_closure_set(v___f_853_, 2, v_inst_842_);
lean_closure_set(v___f_853_, 3, v_fst_850_);
lean_closure_set(v___f_853_, 4, v_fst_851_);
lean_closure_set(v___f_853_, 5, v_toPure_843_);
lean_closure_set(v___f_853_, 6, v_toBind_844_);
lean_closure_set(v___f_853_, 7, v_inst_845_);
lean_closure_set(v___f_853_, 8, v_inst_846_);
lean_closure_set(v___f_853_, 9, v_snd_852_);
v___x_854_ = lean_apply_4(v_toBind_844_, lean_box(0), lean_box(0), v_inst_847_, v___f_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_view_862_){
_start:
{
lean_object* v_toApplicative_863_; lean_object* v_toBind_864_; lean_object* v_toPure_865_; lean_object* v___f_866_; lean_object* v___x_867_; 
v_toApplicative_863_ = lean_ctor_get(v_inst_855_, 0);
v_toBind_864_ = lean_ctor_get(v_inst_855_, 1);
lean_inc_n(v_toBind_864_, 2);
v_toPure_865_ = lean_ctor_get(v_toApplicative_863_, 1);
lean_inc_ref(v_inst_855_);
lean_inc(v_toPure_865_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__8), 9, 8);
lean_closure_set(v___f_866_, 0, v_inst_858_);
lean_closure_set(v___f_866_, 1, v_inst_860_);
lean_closure_set(v___f_866_, 2, v_inst_861_);
lean_closure_set(v___f_866_, 3, v_toPure_865_);
lean_closure_set(v___f_866_, 4, v_toBind_864_);
lean_closure_set(v___f_866_, 5, v_inst_855_);
lean_closure_set(v___f_866_, 6, v_inst_859_);
lean_closure_set(v___f_866_, 7, v_inst_856_);
v___x_867_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_862_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 2, 1);
lean_closure_set(v___f_869_, 0, v___f_866_);
v___x_870_ = l_Lean_throwError___redArg(v_inst_855_, v_inst_857_, v_a_868_);
v___x_871_ = lean_apply_4(v_toBind_864_, lean_box(0), lean_box(0), v___x_870_, v___f_869_);
return v___x_871_;
}
else
{
lean_object* v_a_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_inc(v_toPure_865_);
lean_dec_ref(v_inst_857_);
lean_dec_ref(v_inst_855_);
v_a_872_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_867_, 1);
v___f_873_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 2, 1);
lean_closure_set(v___f_873_, 0, v___f_866_);
v___x_874_ = lean_apply_2(v_toPure_865_, lean_box(0), v_a_872_);
v___x_875_ = lean_apply_4(v_toBind_864_, lean_box(0), lean_box(0), v___x_874_, v___f_873_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_view_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_reportVersoParseFailure___redArg(v_inst_876_, v_inst_877_, v_inst_878_, v_inst_879_, v_inst_880_, v_inst_881_, v_inst_882_, v_view_883_);
lean_dec_ref(v_view_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_m_885_, lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_view_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_reportVersoParseFailure___redArg(v_inst_886_, v_inst_887_, v_inst_888_, v_inst_889_, v_inst_890_, v_inst_891_, v_inst_892_, v_view_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_m_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_view_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_reportVersoParseFailure(v_m_895_, v_inst_896_, v_inst_897_, v_inst_898_, v_inst_899_, v_inst_900_, v_inst_901_, v_inst_902_, v_view_903_);
lean_dec_ref(v_view_903_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_905_, lean_object* v_declName_906_, lean_object* v_binders_907_, lean_object* v___x_908_, uint8_t v___x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_905_) == 0)
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Doc_DocM_exec___redArg(v_declName_906_, v_binders_907_, v___x_908_, v___x_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_917_;
}
else
{
lean_object* v_toCold_918_; lean_object* v_val_919_; lean_object* v_currRecDepth_920_; lean_object* v_ref_921_; uint8_t v_diag_922_; uint8_t v_suppressElabErrors_923_; lean_object* v_fileName_924_; lean_object* v_options_925_; lean_object* v_maxRecDepth_926_; lean_object* v_currNamespace_927_; lean_object* v_openDecls_928_; lean_object* v_initHeartbeats_929_; lean_object* v_maxHeartbeats_930_; lean_object* v_quotContext_931_; lean_object* v_currMacroScope_932_; lean_object* v_cancelTk_x3f_933_; lean_object* v_inheritedTraceOptions_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_toCold_918_ = lean_ctor_get(v___y_914_, 0);
v_val_919_ = lean_ctor_get(v_fileMap_x3f_905_, 0);
v_currRecDepth_920_ = lean_ctor_get(v___y_914_, 1);
v_ref_921_ = lean_ctor_get(v___y_914_, 2);
v_diag_922_ = lean_ctor_get_uint8(v___y_914_, sizeof(void*)*3);
v_suppressElabErrors_923_ = lean_ctor_get_uint8(v___y_914_, sizeof(void*)*3 + 1);
v_fileName_924_ = lean_ctor_get(v_toCold_918_, 0);
v_options_925_ = lean_ctor_get(v_toCold_918_, 2);
v_maxRecDepth_926_ = lean_ctor_get(v_toCold_918_, 3);
v_currNamespace_927_ = lean_ctor_get(v_toCold_918_, 4);
v_openDecls_928_ = lean_ctor_get(v_toCold_918_, 5);
v_initHeartbeats_929_ = lean_ctor_get(v_toCold_918_, 6);
v_maxHeartbeats_930_ = lean_ctor_get(v_toCold_918_, 7);
v_quotContext_931_ = lean_ctor_get(v_toCold_918_, 8);
v_currMacroScope_932_ = lean_ctor_get(v_toCold_918_, 9);
v_cancelTk_x3f_933_ = lean_ctor_get(v_toCold_918_, 10);
v_inheritedTraceOptions_934_ = lean_ctor_get(v_toCold_918_, 11);
lean_inc_ref(v_inheritedTraceOptions_934_);
lean_inc(v_cancelTk_x3f_933_);
lean_inc(v_currMacroScope_932_);
lean_inc(v_quotContext_931_);
lean_inc(v_maxHeartbeats_930_);
lean_inc(v_initHeartbeats_929_);
lean_inc(v_openDecls_928_);
lean_inc(v_currNamespace_927_);
lean_inc(v_maxRecDepth_926_);
lean_inc_ref(v_options_925_);
lean_inc(v_val_919_);
lean_inc_ref(v_fileName_924_);
v___x_935_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_935_, 0, v_fileName_924_);
lean_ctor_set(v___x_935_, 1, v_val_919_);
lean_ctor_set(v___x_935_, 2, v_options_925_);
lean_ctor_set(v___x_935_, 3, v_maxRecDepth_926_);
lean_ctor_set(v___x_935_, 4, v_currNamespace_927_);
lean_ctor_set(v___x_935_, 5, v_openDecls_928_);
lean_ctor_set(v___x_935_, 6, v_initHeartbeats_929_);
lean_ctor_set(v___x_935_, 7, v_maxHeartbeats_930_);
lean_ctor_set(v___x_935_, 8, v_quotContext_931_);
lean_ctor_set(v___x_935_, 9, v_currMacroScope_932_);
lean_ctor_set(v___x_935_, 10, v_cancelTk_x3f_933_);
lean_ctor_set(v___x_935_, 11, v_inheritedTraceOptions_934_);
lean_inc(v_ref_921_);
lean_inc(v_currRecDepth_920_);
v___x_936_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v_currRecDepth_920_);
lean_ctor_set(v___x_936_, 2, v_ref_921_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*3, v_diag_922_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*3 + 1, v_suppressElabErrors_923_);
v___x_937_ = l_Lean_Doc_DocM_exec___redArg(v_declName_906_, v_binders_907_, v___x_908_, v___x_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___x_936_, v___y_915_);
lean_dec_ref_known(v___x_936_, 3);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_938_, lean_object* v_declName_939_, lean_object* v_binders_940_, lean_object* v___x_941_, lean_object* v___x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
uint8_t v___x_9808__boxed_950_; lean_object* v_res_951_; 
v___x_9808__boxed_950_ = lean_unbox(v___x_942_);
v_res_951_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_938_, v_declName_939_, v_binders_940_, v___x_941_, v___x_9808__boxed_950_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v_fileMap_x3f_938_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_952_, size_t v_i_953_, lean_object* v_bs_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_usize_dec_lt(v_i_953_, v_sz_952_);
if (v___x_955_ == 0)
{
return v_bs_954_;
}
else
{
lean_object* v_v_956_; lean_object* v___x_957_; lean_object* v_bs_x27_958_; size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
v_v_956_ = lean_array_uget(v_bs_954_, v_i_953_);
v___x_957_ = lean_unsigned_to_nat(0u);
v_bs_x27_958_ = lean_array_uset(v_bs_954_, v_i_953_, v___x_957_);
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_add(v_i_953_, v___x_959_);
v___x_961_ = lean_array_uset(v_bs_x27_958_, v_i_953_, v_v_956_);
v_i_953_ = v___x_960_;
v_bs_954_ = v___x_961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_963_, lean_object* v_i_964_, lean_object* v_bs_965_){
_start:
{
size_t v_sz_boxed_966_; size_t v_i_boxed_967_; lean_object* v_res_968_; 
v_sz_boxed_966_ = lean_unbox_usize(v_sz_963_);
lean_dec(v_sz_963_);
v_i_boxed_967_ = lean_unbox_usize(v_i_964_);
lean_dec(v_i_964_);
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_966_, v_i_boxed_967_, v_bs_965_);
return v_res_968_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_969_, lean_object* v_opt_970_){
_start:
{
lean_object* v_name_971_; lean_object* v_defValue_972_; lean_object* v_map_973_; lean_object* v___x_974_; 
v_name_971_ = lean_ctor_get(v_opt_970_, 0);
v_defValue_972_ = lean_ctor_get(v_opt_970_, 1);
v_map_973_ = lean_ctor_get(v_opts_969_, 0);
v___x_974_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_973_, v_name_971_);
if (lean_obj_tag(v___x_974_) == 0)
{
uint8_t v___x_975_; 
v___x_975_ = lean_unbox(v_defValue_972_);
return v___x_975_;
}
else
{
lean_object* v_val_976_; 
v_val_976_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v___x_974_, 1);
if (lean_obj_tag(v_val_976_) == 1)
{
uint8_t v_v_977_; 
v_v_977_ = lean_ctor_get_uint8(v_val_976_, 0);
lean_dec_ref_known(v_val_976_, 0);
return v_v_977_;
}
else
{
uint8_t v___x_978_; 
lean_dec(v_val_976_);
v___x_978_ = lean_unbox(v_defValue_972_);
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_979_, lean_object* v_opt_980_){
_start:
{
uint8_t v_res_981_; lean_object* v_r_982_; 
v_res_981_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_979_, v_opt_980_);
lean_dec_ref(v_opt_980_);
lean_dec_ref(v_opts_979_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; lean_object* v_env_990_; lean_object* v___x_991_; lean_object* v_toCold_992_; lean_object* v_mctx_993_; lean_object* v_lctx_994_; lean_object* v_options_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_989_ = lean_st_ref_get(v___y_987_);
v_env_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc_ref(v_env_990_);
lean_dec(v___x_989_);
v___x_991_ = lean_st_ref_get(v___y_985_);
v_toCold_992_ = lean_ctor_get(v___y_986_, 0);
v_mctx_993_ = lean_ctor_get(v___x_991_, 0);
lean_inc_ref(v_mctx_993_);
lean_dec(v___x_991_);
v_lctx_994_ = lean_ctor_get(v___y_984_, 2);
v_options_995_ = lean_ctor_get(v_toCold_992_, 2);
lean_inc_ref(v_options_995_);
lean_inc_ref(v_lctx_994_);
v___x_996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_996_, 0, v_env_990_);
lean_ctor_set(v___x_996_, 1, v_mctx_993_);
lean_ctor_set(v___x_996_, 2, v_lctx_994_);
lean_ctor_set(v___x_996_, 3, v_options_995_);
v___x_997_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_msgData_983_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_1014_, uint8_t v___y_1015_, lean_object* v_x_1016_){
_start:
{
if (lean_obj_tag(v_x_1016_) == 1)
{
lean_object* v_pre_1017_; 
v_pre_1017_ = lean_ctor_get(v_x_1016_, 0);
switch(lean_obj_tag(v_pre_1017_))
{
case 1:
{
lean_object* v_pre_1018_; 
v_pre_1018_ = lean_ctor_get(v_pre_1017_, 0);
switch(lean_obj_tag(v_pre_1018_))
{
case 0:
{
lean_object* v_str_1019_; lean_object* v_str_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_str_1019_ = lean_ctor_get(v_x_1016_, 1);
v_str_1020_ = lean_ctor_get(v_pre_1017_, 1);
v___x_1021_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1022_ = lean_string_dec_eq(v_str_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1024_ = lean_string_dec_eq(v_str_1020_, v___x_1023_);
if (v___x_1024_ == 0)
{
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1026_ = lean_string_dec_eq(v_str_1019_, v___x_1025_);
if (v___x_1026_ == 0)
{
return v___x_1026_;
}
else
{
return v_suppressElabErrors_1014_;
}
}
}
else
{
lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1028_ = lean_string_dec_eq(v_str_1019_, v___x_1027_);
if (v___x_1028_ == 0)
{
return v___x_1028_;
}
else
{
return v_suppressElabErrors_1014_;
}
}
}
case 1:
{
lean_object* v_pre_1029_; 
v_pre_1029_ = lean_ctor_get(v_pre_1018_, 0);
if (lean_obj_tag(v_pre_1029_) == 0)
{
lean_object* v_str_1030_; lean_object* v_str_1031_; lean_object* v_str_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_str_1030_ = lean_ctor_get(v_x_1016_, 1);
v_str_1031_ = lean_ctor_get(v_pre_1017_, 1);
v_str_1032_ = lean_ctor_get(v_pre_1018_, 1);
v___x_1033_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1034_ = lean_string_dec_eq(v_str_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1036_ = lean_string_dec_eq(v_str_1031_, v___x_1035_);
if (v___x_1036_ == 0)
{
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1038_ = lean_string_dec_eq(v_str_1030_, v___x_1037_);
if (v___x_1038_ == 0)
{
return v___x_1038_;
}
else
{
return v_suppressElabErrors_1014_;
}
}
}
}
else
{
return v___y_1015_;
}
}
default: 
{
return v___y_1015_;
}
}
}
case 0:
{
lean_object* v_str_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_str_1039_ = lean_ctor_get(v_x_1016_, 1);
v___x_1040_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1041_ = lean_string_dec_eq(v_str_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
return v___x_1041_;
}
else
{
return v_suppressElabErrors_1014_;
}
}
default: 
{
return v___y_1015_;
}
}
}
else
{
return v___y_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1042_, lean_object* v___y_1043_, lean_object* v_x_1044_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1045_; uint8_t v___y_9907__boxed_1046_; uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_suppressElabErrors_boxed_1045_ = lean_unbox(v_suppressElabErrors_1042_);
v___y_9907__boxed_1046_ = lean_unbox(v___y_1043_);
v_res_1047_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_1045_, v___y_9907__boxed_1046_, v_x_1044_);
lean_dec(v_x_1044_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_1049_, lean_object* v_msgData_1050_, uint8_t v_severity_1051_, uint8_t v_isSilent_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___y_1059_; lean_object* v___y_1060_; uint8_t v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; uint8_t v___y_1065_; lean_object* v_currNamespace_1066_; lean_object* v_openDecls_1067_; lean_object* v___y_1068_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1099_; uint8_t v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; uint8_t v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1128_; uint8_t v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; uint8_t v___y_1139_; uint8_t v___y_1140_; lean_object* v___y_1141_; uint8_t v___y_1142_; uint8_t v___x_1147_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; uint8_t v___y_1156_; uint8_t v___y_1157_; uint8_t v___y_1159_; uint8_t v___x_1177_; 
v___x_1147_ = 2;
v___x_1177_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1051_, v___x_1147_);
if (v___x_1177_ == 0)
{
v___y_1159_ = v___x_1177_;
goto v___jp_1158_;
}
else
{
uint8_t v___x_1178_; 
lean_inc_ref(v_msgData_1050_);
v___x_1178_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1050_);
v___y_1159_ = v___x_1178_;
goto v___jp_1158_;
}
v___jp_1058_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v_env_1073_; lean_object* v_nextMacroScope_1074_; lean_object* v_ngen_1075_; lean_object* v_auxDeclNGen_1076_; lean_object* v_traceState_1077_; lean_object* v_cache_1078_; lean_object* v_messages_1079_; lean_object* v_infoState_1080_; lean_object* v_snapshotTasks_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1092_; 
lean_inc(v_openDecls_1067_);
lean_inc(v_currNamespace_1066_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_currNamespace_1066_);
lean_ctor_set(v___x_1069_, 1, v_openDecls_1067_);
v___x_1070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___y_1062_);
lean_inc_ref(v___y_1064_);
lean_inc_ref(v___y_1060_);
v___x_1071_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1071_, 0, v___y_1060_);
lean_ctor_set(v___x_1071_, 1, v___y_1063_);
lean_ctor_set(v___x_1071_, 2, v___y_1059_);
lean_ctor_set(v___x_1071_, 3, v___y_1064_);
lean_ctor_set(v___x_1071_, 4, v___x_1070_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*5, v___y_1061_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*5 + 1, v___y_1065_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*5 + 2, v_isSilent_1052_);
v___x_1072_ = lean_st_ref_take(v___y_1068_);
v_env_1073_ = lean_ctor_get(v___x_1072_, 0);
v_nextMacroScope_1074_ = lean_ctor_get(v___x_1072_, 1);
v_ngen_1075_ = lean_ctor_get(v___x_1072_, 2);
v_auxDeclNGen_1076_ = lean_ctor_get(v___x_1072_, 3);
v_traceState_1077_ = lean_ctor_get(v___x_1072_, 4);
v_cache_1078_ = lean_ctor_get(v___x_1072_, 5);
v_messages_1079_ = lean_ctor_get(v___x_1072_, 6);
v_infoState_1080_ = lean_ctor_get(v___x_1072_, 7);
v_snapshotTasks_1081_ = lean_ctor_get(v___x_1072_, 8);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1083_ = v___x_1072_;
v_isShared_1084_ = v_isSharedCheck_1092_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snapshotTasks_1081_);
lean_inc(v_infoState_1080_);
lean_inc(v_messages_1079_);
lean_inc(v_cache_1078_);
lean_inc(v_traceState_1077_);
lean_inc(v_auxDeclNGen_1076_);
lean_inc(v_ngen_1075_);
lean_inc(v_nextMacroScope_1074_);
lean_inc(v_env_1073_);
lean_dec(v___x_1072_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1092_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = l_Lean_MessageLog_add(v___x_1071_, v_messages_1079_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 6, v___x_1086_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_env_1073_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_nextMacroScope_1074_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_ngen_1075_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_auxDeclNGen_1076_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_traceState_1077_);
lean_ctor_set(v_reuseFailAlloc_1091_, 5, v_cache_1078_);
lean_ctor_set(v_reuseFailAlloc_1091_, 6, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1091_, 7, v_infoState_1080_);
lean_ctor_set(v_reuseFailAlloc_1091_, 8, v_snapshotTasks_1081_);
v___x_1088_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_st_ref_put(v___y_1068_, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1085_);
return v___x_1090_;
}
}
}
v___jp_1093_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1119_; 
v___x_1104_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1050_);
v___x_1105_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_1104_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1119_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_inc_ref_n(v___y_1101_, 2);
v___x_1110_ = l_Lean_FileMap_toPosition(v___y_1101_, v___y_1097_);
lean_dec(v___y_1097_);
v___x_1111_ = l_Lean_FileMap_toPosition(v___y_1101_, v___y_1103_);
lean_dec(v___y_1103_);
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
v___x_1113_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_1099_ == 0)
{
lean_del_object(v___x_1108_);
lean_dec_ref(v___y_1095_);
v___y_1059_ = v___x_1112_;
v___y_1060_ = v___y_1098_;
v___y_1061_ = v___y_1100_;
v___y_1062_ = v_a_1106_;
v___y_1063_ = v___x_1110_;
v___y_1064_ = v___x_1113_;
v___y_1065_ = v___y_1102_;
v_currNamespace_1066_ = v___y_1094_;
v_openDecls_1067_ = v___y_1096_;
v___y_1068_ = v___y_1056_;
goto v___jp_1058_;
}
else
{
uint8_t v___x_1114_; 
lean_inc(v_a_1106_);
v___x_1114_ = l_Lean_MessageData_hasTag(v___y_1095_, v_a_1106_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_dec_ref_known(v___x_1112_, 1);
lean_dec_ref(v___x_1110_);
lean_dec(v_a_1106_);
v___x_1115_ = lean_box(0);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1115_);
v___x_1117_ = v___x_1108_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
else
{
lean_del_object(v___x_1108_);
v___y_1059_ = v___x_1112_;
v___y_1060_ = v___y_1098_;
v___y_1061_ = v___y_1100_;
v___y_1062_ = v_a_1106_;
v___y_1063_ = v___x_1110_;
v___y_1064_ = v___x_1113_;
v___y_1065_ = v___y_1102_;
v_currNamespace_1066_ = v___y_1094_;
v_openDecls_1067_ = v___y_1096_;
v___y_1068_ = v___y_1056_;
goto v___jp_1058_;
}
}
}
}
v___jp_1120_:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Syntax_getTailPos_x3f(v___y_1124_, v___y_1126_);
lean_dec(v___y_1124_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_inc(v___y_1130_);
v___y_1094_ = v___y_1121_;
v___y_1095_ = v___y_1123_;
v___y_1096_ = v___y_1122_;
v___y_1097_ = v___y_1130_;
v___y_1098_ = v___y_1125_;
v___y_1099_ = v___y_1127_;
v___y_1100_ = v___y_1126_;
v___y_1101_ = v___y_1128_;
v___y_1102_ = v___y_1129_;
v___y_1103_ = v___y_1130_;
goto v___jp_1093_;
}
else
{
lean_object* v_val_1132_; 
v_val_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___y_1094_ = v___y_1121_;
v___y_1095_ = v___y_1123_;
v___y_1096_ = v___y_1122_;
v___y_1097_ = v___y_1130_;
v___y_1098_ = v___y_1125_;
v___y_1099_ = v___y_1127_;
v___y_1100_ = v___y_1126_;
v___y_1101_ = v___y_1128_;
v___y_1102_ = v___y_1129_;
v___y_1103_ = v_val_1132_;
goto v___jp_1093_;
}
}
v___jp_1133_:
{
lean_object* v_ref_1143_; lean_object* v___x_1144_; 
v_ref_1143_ = l_Lean_replaceRef(v_ref_1049_, v___y_1137_);
v___x_1144_ = l_Lean_Syntax_getPos_x3f(v_ref_1143_, v___y_1140_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
v___y_1121_ = v___y_1134_;
v___y_1122_ = v___y_1136_;
v___y_1123_ = v___y_1135_;
v___y_1124_ = v_ref_1143_;
v___y_1125_ = v___y_1138_;
v___y_1126_ = v___y_1140_;
v___y_1127_ = v___y_1139_;
v___y_1128_ = v___y_1141_;
v___y_1129_ = v___y_1142_;
v___y_1130_ = v___x_1145_;
goto v___jp_1120_;
}
else
{
lean_object* v_val_1146_; 
v_val_1146_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_val_1146_);
lean_dec_ref_known(v___x_1144_, 1);
v___y_1121_ = v___y_1134_;
v___y_1122_ = v___y_1136_;
v___y_1123_ = v___y_1135_;
v___y_1124_ = v_ref_1143_;
v___y_1125_ = v___y_1138_;
v___y_1126_ = v___y_1140_;
v___y_1127_ = v___y_1139_;
v___y_1128_ = v___y_1141_;
v___y_1129_ = v___y_1142_;
v___y_1130_ = v_val_1146_;
goto v___jp_1120_;
}
}
v___jp_1148_:
{
if (v___y_1157_ == 0)
{
v___y_1134_ = v___y_1150_;
v___y_1135_ = v___y_1152_;
v___y_1136_ = v___y_1151_;
v___y_1137_ = v___y_1154_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1156_;
v___y_1140_ = v___y_1155_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v_severity_1051_;
goto v___jp_1133_;
}
else
{
v___y_1134_ = v___y_1150_;
v___y_1135_ = v___y_1152_;
v___y_1136_ = v___y_1151_;
v___y_1137_ = v___y_1154_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1156_;
v___y_1140_ = v___y_1155_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___x_1147_;
goto v___jp_1133_;
}
}
v___jp_1158_:
{
if (v___y_1159_ == 0)
{
lean_object* v_toCold_1160_; lean_object* v_ref_1161_; uint8_t v_suppressElabErrors_1162_; lean_object* v_fileName_1163_; lean_object* v_fileMap_1164_; lean_object* v_options_1165_; lean_object* v_currNamespace_1166_; lean_object* v_openDecls_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___f_1170_; uint8_t v___x_1171_; uint8_t v___x_1172_; 
v_toCold_1160_ = lean_ctor_get(v___y_1055_, 0);
v_ref_1161_ = lean_ctor_get(v___y_1055_, 2);
v_suppressElabErrors_1162_ = lean_ctor_get_uint8(v___y_1055_, sizeof(void*)*3 + 1);
v_fileName_1163_ = lean_ctor_get(v_toCold_1160_, 0);
v_fileMap_1164_ = lean_ctor_get(v_toCold_1160_, 1);
v_options_1165_ = lean_ctor_get(v_toCold_1160_, 2);
v_currNamespace_1166_ = lean_ctor_get(v_toCold_1160_, 4);
v_openDecls_1167_ = lean_ctor_get(v_toCold_1160_, 5);
v___x_1168_ = lean_box(v_suppressElabErrors_1162_);
v___x_1169_ = lean_box(v___y_1159_);
v___f_1170_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1170_, 0, v___x_1168_);
lean_closure_set(v___f_1170_, 1, v___x_1169_);
v___x_1171_ = 1;
v___x_1172_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1051_, v___x_1171_);
if (v___x_1172_ == 0)
{
v___y_1149_ = v_fileName_1163_;
v___y_1150_ = v_currNamespace_1166_;
v___y_1151_ = v_openDecls_1167_;
v___y_1152_ = v___f_1170_;
v___y_1153_ = v_fileMap_1164_;
v___y_1154_ = v_ref_1161_;
v___y_1155_ = v___y_1159_;
v___y_1156_ = v_suppressElabErrors_1162_;
v___y_1157_ = v___x_1172_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = l_Lean_warningAsError;
v___x_1174_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1165_, v___x_1173_);
v___y_1149_ = v_fileName_1163_;
v___y_1150_ = v_currNamespace_1166_;
v___y_1151_ = v_openDecls_1167_;
v___y_1152_ = v___f_1170_;
v___y_1153_ = v_fileMap_1164_;
v___y_1154_ = v_ref_1161_;
v___y_1155_ = v___y_1159_;
v___y_1156_ = v_suppressElabErrors_1162_;
v___y_1157_ = v___x_1174_;
goto v___jp_1148_;
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v_msgData_1050_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_1179_, lean_object* v_msgData_1180_, lean_object* v_severity_1181_, lean_object* v_isSilent_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v_severity_boxed_1188_; uint8_t v_isSilent_boxed_1189_; lean_object* v_res_1190_; 
v_severity_boxed_1188_ = lean_unbox(v_severity_1181_);
v_isSilent_boxed_1189_ = lean_unbox(v_isSilent_1182_);
v_res_1190_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1179_, v_msgData_1180_, v_severity_boxed_1188_, v_isSilent_boxed_1189_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v_ref_1179_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_1191_, size_t v_sz_1192_, size_t v_i_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_usize_dec_lt(v_i_1193_, v_sz_1192_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v_b_1194_);
return v___x_1203_;
}
else
{
lean_object* v_ref_1204_; lean_object* v_a_1205_; uint8_t v_severity_1206_; uint8_t v_isSilent_1207_; lean_object* v_data_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_ref_1204_ = lean_ctor_get(v___y_1199_, 2);
v_a_1205_ = lean_array_uget_borrowed(v_as_1191_, v_i_1193_);
v_severity_1206_ = lean_ctor_get_uint8(v_a_1205_, sizeof(void*)*5 + 1);
v_isSilent_1207_ = lean_ctor_get_uint8(v_a_1205_, sizeof(void*)*5 + 2);
v_data_1208_ = lean_ctor_get(v_a_1205_, 4);
v___x_1209_ = lean_box(0);
lean_inc(v_data_1208_);
v___x_1210_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1204_, v_data_1208_, v_severity_1206_, v_isSilent_1207_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1210_) == 0)
{
size_t v___x_1211_; size_t v___x_1212_; 
lean_dec_ref_known(v___x_1210_, 1);
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_add(v_i_1193_, v___x_1211_);
v_i_1193_ = v___x_1212_;
v_b_1194_ = v___x_1209_;
goto _start;
}
else
{
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_1214_, lean_object* v_sz_1215_, lean_object* v_i_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
size_t v_sz_boxed_1225_; size_t v_i_boxed_1226_; lean_object* v_res_1227_; 
v_sz_boxed_1225_ = lean_unbox_usize(v_sz_1215_);
lean_dec(v_sz_1215_);
v_i_boxed_1226_ = lean_unbox_usize(v_i_1216_);
lean_dec(v_i_1216_);
v_res_1227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_1214_, v_sz_boxed_1225_, v_i_boxed_1226_, v_b_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v_as_1214_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v_infoState_1232_; lean_object* v_env_1233_; lean_object* v_nextMacroScope_1234_; lean_object* v_ngen_1235_; lean_object* v_auxDeclNGen_1236_; lean_object* v_traceState_1237_; lean_object* v_cache_1238_; lean_object* v_messages_1239_; lean_object* v_snapshotTasks_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1260_; 
v___x_1231_ = lean_st_ref_take(v___y_1229_);
v_infoState_1232_ = lean_ctor_get(v___x_1231_, 7);
v_env_1233_ = lean_ctor_get(v___x_1231_, 0);
v_nextMacroScope_1234_ = lean_ctor_get(v___x_1231_, 1);
v_ngen_1235_ = lean_ctor_get(v___x_1231_, 2);
v_auxDeclNGen_1236_ = lean_ctor_get(v___x_1231_, 3);
v_traceState_1237_ = lean_ctor_get(v___x_1231_, 4);
v_cache_1238_ = lean_ctor_get(v___x_1231_, 5);
v_messages_1239_ = lean_ctor_get(v___x_1231_, 6);
v_snapshotTasks_1240_ = lean_ctor_get(v___x_1231_, 8);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1242_ = v___x_1231_;
v_isShared_1243_ = v_isSharedCheck_1260_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snapshotTasks_1240_);
lean_inc(v_infoState_1232_);
lean_inc(v_messages_1239_);
lean_inc(v_cache_1238_);
lean_inc(v_traceState_1237_);
lean_inc(v_auxDeclNGen_1236_);
lean_inc(v_ngen_1235_);
lean_inc(v_nextMacroScope_1234_);
lean_inc(v_env_1233_);
lean_dec(v___x_1231_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1260_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_assignment_1244_; lean_object* v_lazyAssignment_1245_; lean_object* v_trees_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1259_; 
v_assignment_1244_ = lean_ctor_get(v_infoState_1232_, 0);
v_lazyAssignment_1245_ = lean_ctor_get(v_infoState_1232_, 1);
v_trees_1246_ = lean_ctor_get(v_infoState_1232_, 2);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_infoState_1232_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1248_ = v_infoState_1232_;
v_isShared_1249_ = v_isSharedCheck_1259_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_trees_1246_);
lean_inc(v_lazyAssignment_1245_);
lean_inc(v_assignment_1244_);
lean_dec(v_infoState_1232_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1259_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_box(0);
if (v_isShared_1249_ == 0)
{
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_assignment_1244_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_lazyAssignment_1245_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_trees_1246_);
v___x_1252_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*3, v_flag_1228_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 7, v___x_1252_);
v___x_1254_ = v___x_1242_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_env_1233_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_nextMacroScope_1234_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_ngen_1235_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_auxDeclNGen_1236_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_traceState_1237_);
lean_ctor_set(v_reuseFailAlloc_1257_, 5, v_cache_1238_);
lean_ctor_set(v_reuseFailAlloc_1257_, 6, v_messages_1239_);
lean_ctor_set(v_reuseFailAlloc_1257_, 7, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1257_, 8, v_snapshotTasks_1240_);
v___x_1254_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_st_ref_put(v___y_1229_, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1250_);
return v___x_1256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v_flag_boxed_1264_; lean_object* v_res_1265_; 
v_flag_boxed_1264_ = lean_unbox(v_flag_1261_);
v_res_1265_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1264_, v___y_1262_);
lean_dec(v___y_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v_infoState_1276_; uint8_t v_enabled_1277_; lean_object* v_a_1279_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1275_ = lean_st_ref_get(v___y_1273_);
v_infoState_1276_ = lean_ctor_get(v___x_1275_, 7);
lean_inc_ref(v_infoState_1276_);
lean_dec(v___x_1275_);
v_enabled_1277_ = lean_ctor_get_uint8(v_infoState_1276_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1276_);
v___x_1289_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1266_, v___y_1273_);
lean_dec_ref(v___x_1289_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
v___x_1290_ = lean_apply_7(v_x_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, lean_box(0));
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1292_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1277_, v___y_1273_);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1292_, 0);
lean_dec(v_unused_1300_);
v___x_1294_ = v___x_1292_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v___x_1292_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v_a_1291_);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1291_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1301_; 
v_a_1301_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1290_, 1);
v_a_1279_ = v_a_1301_;
goto v___jp_1278_;
}
v___jp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v___x_1280_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1277_, v___y_1273_);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v___x_1280_, 0);
lean_dec(v_unused_1288_);
v___x_1282_ = v___x_1280_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_dec(v___x_1280_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 1);
lean_ctor_set(v___x_1282_, 0, v_a_1279_);
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1279_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1302_, lean_object* v_x_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v_flag_boxed_1311_; lean_object* v_res_1312_; 
v_flag_boxed_1311_ = lean_unbox(v_flag_1302_);
v_res_1312_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1311_, v_x_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1313_, lean_object* v_binders_1314_, lean_object* v_blocks_1315_, lean_object* v_fileMap_x3f_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1322_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v_a_1327_; size_t v_sz_1345_; size_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___y_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v_sz_1345_ = lean_array_size(v_blocks_1315_);
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1345_, v___x_1346_, v_blocks_1315_);
v___x_1348_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1348_, 0, v___x_1347_);
v___x_1349_ = 1;
v___x_1350_ = lean_box(v___x_1349_);
v___y_1351_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1351_, 0, v_fileMap_x3f_1316_);
lean_closure_set(v___y_1351_, 1, v_declName_1313_);
lean_closure_set(v___y_1351_, 2, v_binders_1314_);
lean_closure_set(v___y_1351_, 3, v___x_1348_);
lean_closure_set(v___y_1351_, 4, v___x_1350_);
v___x_1352_ = 0;
v___x_1353_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1352_, v___y_1351_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1355_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1355_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1322_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l_Lean_Core_setMessageLog___redArg(v_a_1325_, v_a_1322_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; size_t v_sz_1360_; lean_object* v___x_1361_; 
lean_dec_ref_known(v___x_1357_, 1);
v___x_1358_ = l_Lean_MessageLog_toArray(v_a_1356_);
lean_dec(v_a_1356_);
v___x_1359_ = lean_box(0);
v_sz_1360_ = lean_array_size(v___x_1358_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1358_, v_sz_1360_, v___x_1346_, v___x_1359_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec_ref(v___x_1358_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1386_; 
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v___x_1361_, 0);
lean_dec(v_unused_1387_);
v___x_1363_ = v___x_1361_;
v_isShared_1364_ = v_isSharedCheck_1386_;
goto v_resetjp_1362_;
}
else
{
lean_dec(v___x_1361_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1386_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1385_; 
v_fst_1365_ = lean_ctor_get(v_a_1354_, 0);
v_snd_1366_ = lean_ctor_get(v_a_1354_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_a_1354_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1368_ = v_a_1354_;
v_isShared_1369_ = v_isSharedCheck_1385_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_snd_1366_);
lean_inc(v_fst_1365_);
lean_dec(v_a_1354_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1385_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1384_; 
v_fst_1370_ = lean_ctor_get(v_fst_1365_, 0);
v_snd_1371_ = lean_ctor_get(v_fst_1365_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_fst_1365_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1373_ = v_fst_1365_;
v_isShared_1374_ = v_isSharedCheck_1384_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_inc(v_fst_1370_);
lean_dec(v_fst_1365_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1384_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_fst_1370_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_snd_1371_);
v___x_1376_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1378_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1376_);
v___x_1378_ = v___x_1368_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_snd_1366_);
v___x_1378_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1380_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1378_);
v___x_1380_ = v___x_1363_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_a_1354_);
v_a_1388_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1361_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1361_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_a_1356_);
lean_dec(v_a_1354_);
v_a_1396_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1357_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1357_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
else
{
lean_object* v_a_1404_; 
lean_dec(v_a_1354_);
v_a_1404_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1355_, 1);
v_a_1327_ = v_a_1404_;
goto v___jp_1326_;
}
}
else
{
lean_object* v_a_1405_; 
v_a_1405_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1353_, 1);
v_a_1327_ = v_a_1405_;
goto v___jp_1326_;
}
v___jp_1326_:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Core_setMessageLog___redArg(v_a_1325_, v_a_1322_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v___x_1328_, 0);
lean_dec(v_unused_1336_);
v___x_1330_ = v___x_1328_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_dec(v___x_1328_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 1);
lean_ctor_set(v___x_1330_, 0, v_a_1327_);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1327_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v_a_1327_);
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v_fileMap_x3f_1316_);
lean_dec_ref(v_blocks_1315_);
lean_dec(v_binders_1314_);
lean_dec(v_declName_1313_);
v_a_1406_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1324_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1324_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1414_, lean_object* v_binders_1415_, lean_object* v_blocks_1416_, lean_object* v_fileMap_x3f_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1414_, v_binders_1415_, v_blocks_1416_, v_fileMap_x3f_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1426_, v___y_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v_flag_boxed_1443_; lean_object* v_res_1444_; 
v_flag_boxed_1443_ = lean_unbox(v_flag_1435_);
v_res_1444_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1443_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1445_, uint8_t v_flag_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1446_, v_x_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_flag_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_flag_boxed_1466_; lean_object* v_res_1467_; 
v_flag_boxed_1466_ = lean_unbox(v_flag_1457_);
v_res_1467_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1456_, v_flag_boxed_1466_, v_x_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1468_, lean_object* v_msgData_1469_, uint8_t v_severity_1470_, uint8_t v_isSilent_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1468_, v_msgData_1469_, v_severity_1470_, v_isSilent_1471_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1480_, lean_object* v_msgData_1481_, lean_object* v_severity_1482_, lean_object* v_isSilent_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_severity_boxed_1491_; uint8_t v_isSilent_boxed_1492_; lean_object* v_res_1493_; 
v_severity_boxed_1491_ = lean_unbox(v_severity_1482_);
v_isSilent_boxed_1492_ = lean_unbox(v_isSilent_1483_);
v_res_1493_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1480_, v_msgData_1481_, v_severity_boxed_1491_, v_isSilent_boxed_1492_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v_ref_1480_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1494_, uint8_t v_severity_1495_, uint8_t v_isSilent_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_ref_1502_; lean_object* v___x_1503_; 
v_ref_1502_ = lean_ctor_get(v___y_1499_, 2);
v___x_1503_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1502_, v_msgData_1494_, v_severity_1495_, v_isSilent_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1504_, lean_object* v_severity_1505_, lean_object* v_isSilent_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v_severity_boxed_1512_; uint8_t v_isSilent_boxed_1513_; lean_object* v_res_1514_; 
v_severity_boxed_1512_ = lean_unbox(v_severity_1505_);
v_isSilent_boxed_1513_ = lean_unbox(v_isSilent_1506_);
v_res_1514_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1504_, v_severity_boxed_1512_, v_isSilent_boxed_1513_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
uint8_t v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = 2;
v___x_1524_ = 0;
v___x_1525_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1515_, v___x_1523_, v___x_1524_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1535_, size_t v_sz_1536_, size_t v_i_1537_, lean_object* v_b_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_usize_dec_lt(v_i_1537_, v_sz_1536_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_b_1538_);
return v___x_1547_;
}
else
{
lean_object* v_a_1548_; lean_object* v_snd_1549_; lean_object* v_snd_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_a_1548_ = lean_array_uget_borrowed(v_as_1535_, v_i_1537_);
v_snd_1549_ = lean_ctor_get(v_a_1548_, 1);
v_snd_1550_ = lean_ctor_get(v_snd_1549_, 1);
v___x_1551_ = lean_box(0);
lean_inc(v_snd_1550_);
v___x_1552_ = l_Lean_Parser_Error_toString(v_snd_1550_);
v___x_1553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___x_1554_ = l_Lean_MessageData_ofFormat(v___x_1553_);
v___x_1555_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1554_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1555_) == 0)
{
size_t v___x_1556_; size_t v___x_1557_; 
lean_dec_ref_known(v___x_1555_, 1);
v___x_1556_ = ((size_t)1ULL);
v___x_1557_ = lean_usize_add(v_i_1537_, v___x_1556_);
v_i_1537_ = v___x_1557_;
v_b_1538_ = v___x_1551_;
goto _start;
}
else
{
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1559_, lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
size_t v_sz_boxed_1570_; size_t v_i_boxed_1571_; lean_object* v_res_1572_; 
v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1571_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1559_, v_sz_boxed_1570_, v_i_boxed_1571_, v_b_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v_as_1559_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1591_, lean_object* v_binders_1592_, lean_object* v_docComment_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v_toCold_1602_; lean_object* v_env_1603_; lean_object* v_fileName_1604_; lean_object* v_options_1605_; lean_object* v_currNamespace_1606_; lean_object* v_openDecls_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1601_ = lean_st_ref_get(v_a_1599_);
v_toCold_1602_ = lean_ctor_get(v_a_1598_, 0);
v_env_1603_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_ref_n(v_env_1603_, 2);
lean_dec(v___x_1601_);
v_fileName_1604_ = lean_ctor_get(v_toCold_1602_, 0);
v_options_1605_ = lean_ctor_get(v_toCold_1602_, 2);
v_currNamespace_1606_ = lean_ctor_get(v_toCold_1602_, 4);
v_openDecls_1607_ = lean_ctor_get(v_toCold_1602_, 5);
v___x_1608_ = lean_string_utf8_byte_size(v_docComment_1593_);
lean_inc_ref_n(v_docComment_1593_, 2);
v___x_1609_ = l_Lean_FileMap_ofString(v_docComment_1593_);
lean_inc_ref(v___x_1609_);
lean_inc_ref(v_fileName_1604_);
v___x_1610_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1610_, 0, v_docComment_1593_);
lean_ctor_set(v___x_1610_, 1, v_fileName_1604_);
lean_ctor_set(v___x_1610_, 2, v___x_1609_);
lean_ctor_set(v___x_1610_, 3, v___x_1608_);
lean_inc(v_openDecls_1607_);
lean_inc(v_currNamespace_1606_);
lean_inc_ref(v_options_1605_);
v___x_1611_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1611_, 0, v_env_1603_);
lean_ctor_set(v___x_1611_, 1, v_options_1605_);
lean_ctor_set(v___x_1611_, 2, v_currNamespace_1606_);
lean_ctor_set(v___x_1611_, 3, v_openDecls_1607_);
v___x_1612_ = l_Lean_Parser_mkParserState(v_docComment_1593_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__1));
v___x_1615_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1616_ = l_Lean_Parser_getTokenTable(v_env_1603_);
lean_inc_ref(v___x_1616_);
lean_inc_ref(v___x_1611_);
lean_inc_ref_n(v___x_1610_, 2);
v___x_1617_ = l_Lean_Parser_ParserFn_run(v___x_1615_, v___x_1610_, v___x_1611_, v___x_1616_, v___x_1612_);
lean_inc_ref(v___x_1617_);
v___x_1618_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v___x_1610_, v___x_1611_, v___x_1616_, v_docComment_1593_, v___x_1614_, v___x_1617_);
v___x_1619_ = lean_array_get_size(v___x_1618_);
v___x_1620_ = lean_nat_dec_eq(v___x_1619_, v___x_1613_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; size_t v_sz_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v___x_1617_);
lean_dec_ref_known(v___x_1610_, 4);
lean_dec_ref(v___x_1609_);
lean_dec_ref(v_docComment_1593_);
lean_dec(v_binders_1592_);
lean_dec(v_declName_1591_);
v___x_1621_ = lean_box(0);
v_sz_1622_ = lean_array_size(v___x_1618_);
v___x_1623_ = ((size_t)0ULL);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1618_, v_sz_1622_, v___x_1623_, v___x_1621_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
lean_dec_ref(v___x_1618_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1632_; 
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v___x_1624_, 0);
lean_dec(v_unused_1633_);
v___x_1626_ = v___x_1624_;
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
else
{
lean_dec(v___x_1624_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1628_);
v___x_1630_ = v___x_1626_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_a_1634_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1624_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1624_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
else
{
lean_object* v_stxStack_1642_; lean_object* v_pos_1643_; uint8_t v___x_1644_; 
lean_dec_ref(v___x_1618_);
v_stxStack_1642_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref(v_stxStack_1642_);
v_pos_1643_ = lean_ctor_get(v___x_1617_, 2);
lean_inc(v_pos_1643_);
lean_dec_ref(v___x_1617_);
v___x_1644_ = l_Lean_Parser_InputContext_atEnd(v___x_1610_, v_pos_1643_);
lean_dec_ref_known(v___x_1610_, 4);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; uint32_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v_stxStack_1642_);
lean_dec_ref(v___x_1609_);
lean_dec(v_binders_1592_);
lean_dec(v_declName_1591_);
v___x_1645_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__0));
v___x_1646_ = lean_string_utf8_get(v_docComment_1593_, v_pos_1643_);
lean_dec(v_pos_1643_);
lean_dec_ref(v_docComment_1593_);
v___x_1647_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_1648_ = lean_string_push(v___x_1647_, v___x_1646_);
v___x_1649_ = lean_string_append(v___x_1645_, v___x_1648_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__1));
v___x_1651_ = lean_string_append(v___x_1649_, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
v___x_1653_ = l_Lean_MessageData_ofFormat(v___x_1652_);
v___x_1654_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1653_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1662_; 
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1654_, 0);
lean_dec(v_unused_1663_);
v___x_1656_ = v___x_1654_;
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
else
{
lean_dec(v___x_1654_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1658_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_a_1664_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1654_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1654_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v_pos_1643_);
lean_dec_ref(v_docComment_1593_);
v___x_1672_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1642_);
lean_dec_ref(v_stxStack_1642_);
v___x_1673_ = l_Lean_TSyntax_getVersoBlocks(v___x_1672_);
lean_dec(v___x_1672_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1609_);
v___x_1675_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1591_, v_binders_1592_, v___x_1673_, v___x_1674_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1676_, lean_object* v_binders_1677_, lean_object* v_docComment_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_versoDocStringOfText(v_declName_1676_, v_binders_1677_, v_docComment_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1687_, uint8_t v_severity_1688_, uint8_t v_isSilent_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1687_, v_severity_1688_, v_isSilent_1689_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1698_, lean_object* v_severity_1699_, lean_object* v_isSilent_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_severity_boxed_1708_; uint8_t v_isSilent_boxed_1709_; lean_object* v_res_1710_; 
v_severity_boxed_1708_ = lean_unbox(v_severity_1699_);
v_isSilent_boxed_1709_ = lean_unbox(v_isSilent_1700_);
v_res_1710_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1698_, v_severity_boxed_1708_, v_isSilent_boxed_1709_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1710_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v_suppressElabErrors_1711_, uint8_t v___x_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 1)
{
lean_object* v_pre_1714_; 
v_pre_1714_ = lean_ctor_get(v_x_1713_, 0);
switch(lean_obj_tag(v_pre_1714_))
{
case 1:
{
lean_object* v_pre_1715_; 
v_pre_1715_ = lean_ctor_get(v_pre_1714_, 0);
switch(lean_obj_tag(v_pre_1715_))
{
case 0:
{
lean_object* v_str_1716_; lean_object* v_str_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_str_1716_ = lean_ctor_get(v_x_1713_, 1);
v_str_1717_ = lean_ctor_get(v_pre_1714_, 1);
v___x_1718_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1719_ = lean_string_dec_eq(v_str_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1721_ = lean_string_dec_eq(v_str_1717_, v___x_1720_);
if (v___x_1721_ == 0)
{
return v___x_1721_;
}
else
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1723_ = lean_string_dec_eq(v_str_1716_, v___x_1722_);
if (v___x_1723_ == 0)
{
return v___x_1723_;
}
else
{
return v_suppressElabErrors_1711_;
}
}
}
else
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1725_ = lean_string_dec_eq(v_str_1716_, v___x_1724_);
if (v___x_1725_ == 0)
{
return v___x_1725_;
}
else
{
return v_suppressElabErrors_1711_;
}
}
}
case 1:
{
lean_object* v_pre_1726_; 
v_pre_1726_ = lean_ctor_get(v_pre_1715_, 0);
if (lean_obj_tag(v_pre_1726_) == 0)
{
lean_object* v_str_1727_; lean_object* v_str_1728_; lean_object* v_str_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_str_1727_ = lean_ctor_get(v_x_1713_, 1);
v_str_1728_ = lean_ctor_get(v_pre_1714_, 1);
v_str_1729_ = lean_ctor_get(v_pre_1715_, 1);
v___x_1730_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1731_ = lean_string_dec_eq(v_str_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1733_ = lean_string_dec_eq(v_str_1728_, v___x_1732_);
if (v___x_1733_ == 0)
{
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1735_ = lean_string_dec_eq(v_str_1727_, v___x_1734_);
if (v___x_1735_ == 0)
{
return v___x_1735_;
}
else
{
return v_suppressElabErrors_1711_;
}
}
}
}
else
{
return v___x_1712_;
}
}
default: 
{
return v___x_1712_;
}
}
}
case 0:
{
lean_object* v_str_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_str_1736_ = lean_ctor_get(v_x_1713_, 1);
v___x_1737_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1738_ = lean_string_dec_eq(v_str_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
return v___x_1738_;
}
else
{
return v_suppressElabErrors_1711_;
}
}
default: 
{
return v___x_1712_;
}
}
}
else
{
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1739_, lean_object* v___x_1740_, lean_object* v_x_1741_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1742_; uint8_t v___x_9879__boxed_1743_; uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_suppressElabErrors_boxed_1742_ = lean_unbox(v_suppressElabErrors_1739_);
v___x_9879__boxed_1743_ = lean_unbox(v___x_1740_);
v_res_1744_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v_suppressElabErrors_boxed_1742_, v___x_9879__boxed_1743_, v_x_1741_);
lean_dec(v_x_1741_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v_suppressElabErrors_1746_, uint8_t v___x_1747_, lean_object* v_x_1748_){
_start:
{
if (lean_obj_tag(v_x_1748_) == 1)
{
lean_object* v_pre_1749_; 
v_pre_1749_ = lean_ctor_get(v_x_1748_, 0);
switch(lean_obj_tag(v_pre_1749_))
{
case 1:
{
lean_object* v_pre_1750_; 
v_pre_1750_ = lean_ctor_get(v_pre_1749_, 0);
switch(lean_obj_tag(v_pre_1750_))
{
case 0:
{
lean_object* v_str_1751_; lean_object* v_str_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_str_1751_ = lean_ctor_get(v_x_1748_, 1);
v_str_1752_ = lean_ctor_get(v_pre_1749_, 1);
v___x_1753_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1754_ = lean_string_dec_eq(v_str_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1756_ = lean_string_dec_eq(v_str_1752_, v___x_1755_);
if (v___x_1756_ == 0)
{
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1758_ = lean_string_dec_eq(v_str_1751_, v___x_1757_);
if (v___x_1758_ == 0)
{
return v___x_1758_;
}
else
{
return v_suppressElabErrors_1746_;
}
}
}
else
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1760_ = lean_string_dec_eq(v_str_1751_, v___x_1759_);
if (v___x_1760_ == 0)
{
return v___x_1760_;
}
else
{
return v_suppressElabErrors_1746_;
}
}
}
case 1:
{
lean_object* v_pre_1761_; 
v_pre_1761_ = lean_ctor_get(v_pre_1750_, 0);
if (lean_obj_tag(v_pre_1761_) == 0)
{
lean_object* v_str_1762_; lean_object* v_str_1763_; lean_object* v_str_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_str_1762_ = lean_ctor_get(v_x_1748_, 1);
v_str_1763_ = lean_ctor_get(v_pre_1749_, 1);
v_str_1764_ = lean_ctor_get(v_pre_1750_, 1);
v___x_1765_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1766_ = lean_string_dec_eq(v_str_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1768_ = lean_string_dec_eq(v_str_1763_, v___x_1767_);
if (v___x_1768_ == 0)
{
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1770_ = lean_string_dec_eq(v_str_1762_, v___x_1769_);
if (v___x_1770_ == 0)
{
return v___x_1770_;
}
else
{
return v_suppressElabErrors_1746_;
}
}
}
}
else
{
return v___x_1747_;
}
}
default: 
{
return v___x_1747_;
}
}
}
case 0:
{
lean_object* v_str_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_str_1771_ = lean_ctor_get(v_x_1748_, 1);
v___x_1772_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1773_ = lean_string_dec_eq(v_str_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
return v___x_1773_;
}
else
{
return v_suppressElabErrors_1746_;
}
}
default: 
{
return v___x_1747_;
}
}
}
else
{
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1774_, lean_object* v___x_1775_, lean_object* v_x_1776_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1777_; uint8_t v___x_9943__boxed_1778_; uint8_t v_res_1779_; lean_object* v_r_1780_; 
v_suppressElabErrors_boxed_1777_ = lean_unbox(v_suppressElabErrors_1774_);
v___x_9943__boxed_1778_ = lean_unbox(v___x_1775_);
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v_suppressElabErrors_boxed_1777_, v___x_9943__boxed_1778_, v_x_1776_);
lean_dec(v_x_1776_);
v_r_1780_ = lean_box(v_res_1779_);
return v_r_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v_ictx_1781_, lean_object* v___x_1782_, lean_object* v_as_1783_, size_t v_sz_1784_, size_t v_i_1785_, lean_object* v_b_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_a_1791_; uint8_t v___x_1795_; 
v___x_1795_ = lean_usize_dec_lt(v_i_1785_, v_sz_1784_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; 
lean_dec_ref(v_ictx_1781_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v_b_1786_);
return v___x_1796_;
}
else
{
lean_object* v_a_1797_; lean_object* v_snd_1798_; lean_object* v_fst_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1865_; 
v_a_1797_ = lean_array_uget(v_as_1783_, v_i_1785_);
v_snd_1798_ = lean_ctor_get(v_a_1797_, 1);
v_fst_1799_ = lean_ctor_get(v_a_1797_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_a_1797_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1801_ = v_a_1797_;
v_isShared_1802_ = v_isSharedCheck_1865_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1798_);
lean_inc(v_fst_1799_);
lean_dec(v_a_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1865_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_snd_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1863_; 
v_snd_1803_ = lean_ctor_get(v_snd_1798_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_snd_1798_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v_snd_1798_, 0);
lean_dec(v_unused_1864_);
v___x_1805_ = v_snd_1798_;
v_isShared_1806_ = v_isSharedCheck_1863_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_snd_1803_);
lean_dec(v_snd_1798_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1863_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
uint8_t v_suppressElabErrors_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___y_1811_; lean_object* v___y_1812_; 
v_suppressElabErrors_1807_ = lean_ctor_get_uint8(v___y_1787_, sizeof(void*)*3 + 1);
v___x_1808_ = lean_box(0);
lean_inc_ref(v_ictx_1781_);
v___x_1809_ = l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(v_ictx_1781_, v_fst_1799_, v_snd_1803_);
if (v_suppressElabErrors_1807_ == 0)
{
v___y_1811_ = v___y_1787_;
v___y_1812_ = v___y_1788_;
goto v___jp_1810_;
}
else
{
lean_object* v_data_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___f_1861_; uint8_t v___x_1862_; 
v_data_1856_ = lean_ctor_get(v___x_1809_, 4);
lean_inc(v_data_1856_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_nat_dec_eq(v___x_1782_, v___x_1857_);
v___x_1859_ = lean_box(v_suppressElabErrors_1807_);
v___x_1860_ = lean_box(v___x_1858_);
v___f_1861_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1861_, 0, v___x_1859_);
lean_closure_set(v___f_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_MessageData_hasTag(v___f_1861_, v_data_1856_);
if (v___x_1862_ == 0)
{
lean_dec_ref(v___x_1809_);
lean_del_object(v___x_1805_);
lean_del_object(v___x_1801_);
v_a_1791_ = v___x_1808_;
goto v___jp_1790_;
}
else
{
v___y_1811_ = v___y_1787_;
v___y_1812_ = v___y_1788_;
goto v___jp_1810_;
}
}
v___jp_1810_:
{
lean_object* v_toCold_1813_; lean_object* v_fileName_1814_; lean_object* v_pos_1815_; lean_object* v_endPos_1816_; uint8_t v_keepFullRange_1817_; uint8_t v_severity_1818_; uint8_t v_isSilent_1819_; lean_object* v_caption_1820_; lean_object* v_data_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1855_; 
v_toCold_1813_ = lean_ctor_get(v___y_1811_, 0);
v_fileName_1814_ = lean_ctor_get(v___x_1809_, 0);
v_pos_1815_ = lean_ctor_get(v___x_1809_, 1);
v_endPos_1816_ = lean_ctor_get(v___x_1809_, 2);
v_keepFullRange_1817_ = lean_ctor_get_uint8(v___x_1809_, sizeof(void*)*5);
v_severity_1818_ = lean_ctor_get_uint8(v___x_1809_, sizeof(void*)*5 + 1);
v_isSilent_1819_ = lean_ctor_get_uint8(v___x_1809_, sizeof(void*)*5 + 2);
v_caption_1820_ = lean_ctor_get(v___x_1809_, 3);
v_data_1821_ = lean_ctor_get(v___x_1809_, 4);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1823_ = v___x_1809_;
v_isShared_1824_ = v_isSharedCheck_1855_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_data_1821_);
lean_inc(v_caption_1820_);
lean_inc(v_endPos_1816_);
lean_inc(v_pos_1815_);
lean_inc(v_fileName_1814_);
lean_dec(v___x_1809_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1855_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_currNamespace_1825_; lean_object* v_openDecls_1826_; lean_object* v___x_1828_; 
v_currNamespace_1825_ = lean_ctor_get(v_toCold_1813_, 4);
v_openDecls_1826_ = lean_ctor_get(v_toCold_1813_, 5);
lean_inc(v_openDecls_1826_);
lean_inc(v_currNamespace_1825_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v_openDecls_1826_);
lean_ctor_set(v___x_1805_, 0, v_currNamespace_1825_);
v___x_1828_ = v___x_1805_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_currNamespace_1825_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_openDecls_1826_);
v___x_1828_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 4);
lean_ctor_set(v___x_1801_, 1, v_data_1821_);
lean_ctor_set(v___x_1801_, 0, v___x_1828_);
v___x_1830_ = v___x_1801_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_data_1821_);
v___x_1830_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 4, v___x_1830_);
v___x_1832_ = v___x_1823_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_fileName_1814_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_pos_1815_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_endPos_1816_);
lean_ctor_set(v_reuseFailAlloc_1852_, 3, v_caption_1820_);
lean_ctor_set(v_reuseFailAlloc_1852_, 4, v___x_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1852_, sizeof(void*)*5, v_keepFullRange_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1852_, sizeof(void*)*5 + 1, v_severity_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1852_, sizeof(void*)*5 + 2, v_isSilent_1819_);
v___x_1832_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; lean_object* v_env_1834_; lean_object* v_nextMacroScope_1835_; lean_object* v_ngen_1836_; lean_object* v_auxDeclNGen_1837_; lean_object* v_traceState_1838_; lean_object* v_cache_1839_; lean_object* v_messages_1840_; lean_object* v_infoState_1841_; lean_object* v_snapshotTasks_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1851_; 
v___x_1833_ = lean_st_ref_take(v___y_1812_);
v_env_1834_ = lean_ctor_get(v___x_1833_, 0);
v_nextMacroScope_1835_ = lean_ctor_get(v___x_1833_, 1);
v_ngen_1836_ = lean_ctor_get(v___x_1833_, 2);
v_auxDeclNGen_1837_ = lean_ctor_get(v___x_1833_, 3);
v_traceState_1838_ = lean_ctor_get(v___x_1833_, 4);
v_cache_1839_ = lean_ctor_get(v___x_1833_, 5);
v_messages_1840_ = lean_ctor_get(v___x_1833_, 6);
v_infoState_1841_ = lean_ctor_get(v___x_1833_, 7);
v_snapshotTasks_1842_ = lean_ctor_get(v___x_1833_, 8);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1844_ = v___x_1833_;
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_snapshotTasks_1842_);
lean_inc(v_infoState_1841_);
lean_inc(v_messages_1840_);
lean_inc(v_cache_1839_);
lean_inc(v_traceState_1838_);
lean_inc(v_auxDeclNGen_1837_);
lean_inc(v_ngen_1836_);
lean_inc(v_nextMacroScope_1835_);
lean_inc(v_env_1834_);
lean_dec(v___x_1833_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = l_Lean_MessageLog_add(v___x_1832_, v_messages_1840_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 6, v___x_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_env_1834_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_nextMacroScope_1835_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_ngen_1836_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_auxDeclNGen_1837_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_traceState_1838_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v_cache_1839_);
lean_ctor_set(v_reuseFailAlloc_1850_, 6, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1850_, 7, v_infoState_1841_);
lean_ctor_set(v_reuseFailAlloc_1850_, 8, v_snapshotTasks_1842_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_st_ref_put(v___y_1812_, v___x_1848_);
v_a_1791_ = v___x_1808_;
goto v___jp_1790_;
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
v___jp_1790_:
{
size_t v___x_1792_; size_t v___x_1793_; 
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = lean_usize_add(v_i_1785_, v___x_1792_);
v_i_1785_ = v___x_1793_;
v_b_1786_ = v_a_1791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v_ictx_1866_, lean_object* v___x_1867_, lean_object* v_as_1868_, lean_object* v_sz_1869_, lean_object* v_i_1870_, lean_object* v_b_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
size_t v_sz_boxed_1875_; size_t v_i_boxed_1876_; lean_object* v_res_1877_; 
v_sz_boxed_1875_ = lean_unbox_usize(v_sz_1869_);
lean_dec(v_sz_1869_);
v_i_boxed_1876_ = lean_unbox_usize(v_i_1870_);
lean_dec(v_i_1870_);
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v_ictx_1866_, v___x_1867_, v_as_1868_, v_sz_boxed_1875_, v_i_boxed_1876_, v_b_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec_ref(v_as_1868_);
lean_dec(v___x_1867_);
return v_res_1877_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_box(1);
v___x_1879_ = l_Lean_MessageData_ofFormat(v___x_1878_);
return v___x_1879_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__2));
v___x_1884_ = l_Lean_MessageData_ofFormat(v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
return v_x_1885_;
}
else
{
lean_object* v_head_1887_; lean_object* v_tail_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1910_; 
v_head_1887_ = lean_ctor_get(v_x_1886_, 0);
v_tail_1888_ = lean_ctor_get(v_x_1886_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_x_1886_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1890_ = v_x_1886_;
v_isShared_1891_ = v_isSharedCheck_1910_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_tail_1888_);
lean_inc(v_head_1887_);
lean_dec(v_x_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1910_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_before_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1908_; 
v_before_1892_ = lean_ctor_get(v_head_1887_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_head_1887_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; 
v_unused_1909_ = lean_ctor_get(v_head_1887_, 1);
lean_dec(v_unused_1909_);
v___x_1894_ = v_head_1887_;
v_isShared_1895_ = v_isSharedCheck_1908_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_before_1892_);
lean_dec(v_head_1887_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1908_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 7);
lean_ctor_set(v___x_1894_, 1, v___x_1896_);
lean_ctor_set(v___x_1894_, 0, v_x_1885_);
v___x_1898_ = v___x_1894_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_x_1885_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 7);
lean_ctor_set(v___x_1890_, 1, v___x_1899_);
lean_ctor_set(v___x_1890_, 0, v___x_1898_);
v___x_1901_ = v___x_1890_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = l_Lean_MessageData_ofSyntax(v_before_1892_);
v___x_1903_ = l_Lean_indentD(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v_x_1885_ = v___x_1904_;
v_x_1886_ = v_tail_1888_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_1915_ = l_Lean_MessageData_ofFormat(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_1916_, lean_object* v_macroStack_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_toCold_1920_; lean_object* v_options_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v_toCold_1920_ = lean_ctor_get(v___y_1918_, 0);
v_options_1921_ = lean_ctor_get(v_toCold_1920_, 2);
v___x_1922_ = l_Lean_Elab_pp_macroStack;
v___x_1923_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1921_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_dec(v_macroStack_1917_);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_msgData_1916_);
return v___x_1924_;
}
else
{
if (lean_obj_tag(v_macroStack_1917_) == 0)
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_msgData_1916_);
return v___x_1925_;
}
else
{
lean_object* v_head_1926_; lean_object* v_after_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1942_; 
v_head_1926_ = lean_ctor_get(v_macroStack_1917_, 0);
lean_inc(v_head_1926_);
v_after_1927_ = lean_ctor_get(v_head_1926_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_head_1926_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_head_1926_, 0);
lean_dec(v_unused_1943_);
v___x_1929_ = v_head_1926_;
v_isShared_1930_ = v_isSharedCheck_1942_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_after_1927_);
lean_dec(v_head_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1942_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 7);
lean_ctor_set(v___x_1929_, 1, v___x_1931_);
lean_ctor_set(v___x_1929_, 0, v_msgData_1916_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_msgData_1916_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_msgData_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1934_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = l_Lean_MessageData_ofSyntax(v_after_1927_);
v___x_1937_ = l_Lean_indentD(v___x_1936_);
v_msgData_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1938_, 0, v___x_1935_);
lean_ctor_set(v_msgData_1938_, 1, v___x_1937_);
v___x_1939_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__3(v_msgData_1938_, v_macroStack_1917_);
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1944_, lean_object* v_macroStack_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msgData_1944_, v_macroStack_1945_, v___y_1946_);
lean_dec_ref(v___y_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_ref_1957_; lean_object* v_macroStack_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v_a_1961_; lean_object* v___x_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1971_; 
v_ref_1957_ = lean_ctor_get(v___y_1954_, 2);
v_macroStack_1958_ = lean_ctor_get(v___y_1950_, 1);
v___x_1959_ = l_Lean_Elab_getBetterRef(v_ref_1957_, v_macroStack_1958_);
v___x_1960_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_1949_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref(v___x_1960_);
lean_inc(v_macroStack_1958_);
v___x_1962_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_a_1961_, v_macroStack_1958_, v___y_1954_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1959_);
lean_ctor_set(v___x_1967_, 1, v_a_1963_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 1);
lean_ctor_set(v___x_1965_, 0, v___x_1967_);
v___x_1969_ = v___x_1965_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_msg_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_msg_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
uint8_t v___y_1993_; uint8_t v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v_currNamespace_2000_; lean_object* v_openDecls_2001_; lean_object* v___y_2002_; lean_object* v_toCold_2025_; lean_object* v_fileMap_2026_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v_____x_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___x_2108_; 
v_toCold_2025_ = lean_ctor_get(v___y_1986_, 0);
v_fileMap_2026_ = lean_ctor_get(v_toCold_2025_, 1);
v___x_2108_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_1981_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2110_; lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_a_2109_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
else
{
lean_object* v_a_2119_; 
v_a_2119_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2108_, 1);
v_____x_2098_ = v_a_2119_;
v___y_2099_ = v___y_1986_;
v___y_2100_ = v___y_1987_;
goto v___jp_2097_;
}
v___jp_1989_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_box(0);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
return v___x_1991_;
}
v___jp_1992_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v_env_2007_; lean_object* v_nextMacroScope_2008_; lean_object* v_ngen_2009_; lean_object* v_auxDeclNGen_2010_; lean_object* v_traceState_2011_; lean_object* v_cache_2012_; lean_object* v_messages_2013_; lean_object* v_infoState_2014_; lean_object* v_snapshotTasks_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2024_; 
lean_inc(v_openDecls_2001_);
lean_inc(v_currNamespace_2000_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v_currNamespace_2000_);
lean_ctor_set(v___x_2003_, 1, v_openDecls_2001_);
v___x_2004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v___y_1997_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1999_);
v___x_2005_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2005_, 0, v___y_1999_);
lean_ctor_set(v___x_2005_, 1, v___y_1996_);
lean_ctor_set(v___x_2005_, 2, v___y_1998_);
lean_ctor_set(v___x_2005_, 3, v___y_1995_);
lean_ctor_set(v___x_2005_, 4, v___x_2004_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*5, v___y_1994_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*5 + 1, v___y_1993_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*5 + 2, v___y_1994_);
v___x_2006_ = lean_st_ref_take(v___y_2002_);
v_env_2007_ = lean_ctor_get(v___x_2006_, 0);
v_nextMacroScope_2008_ = lean_ctor_get(v___x_2006_, 1);
v_ngen_2009_ = lean_ctor_get(v___x_2006_, 2);
v_auxDeclNGen_2010_ = lean_ctor_get(v___x_2006_, 3);
v_traceState_2011_ = lean_ctor_get(v___x_2006_, 4);
v_cache_2012_ = lean_ctor_get(v___x_2006_, 5);
v_messages_2013_ = lean_ctor_get(v___x_2006_, 6);
v_infoState_2014_ = lean_ctor_get(v___x_2006_, 7);
v_snapshotTasks_2015_ = lean_ctor_get(v___x_2006_, 8);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2017_ = v___x_2006_;
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snapshotTasks_2015_);
lean_inc(v_infoState_2014_);
lean_inc(v_messages_2013_);
lean_inc(v_cache_2012_);
lean_inc(v_traceState_2011_);
lean_inc(v_auxDeclNGen_2010_);
lean_inc(v_ngen_2009_);
lean_inc(v_nextMacroScope_2008_);
lean_inc(v_env_2007_);
lean_dec(v___x_2006_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = l_Lean_MessageLog_add(v___x_2005_, v_messages_2013_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 6, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_env_2007_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_nextMacroScope_2008_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_ngen_2009_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_auxDeclNGen_2010_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v_traceState_2011_);
lean_ctor_set(v_reuseFailAlloc_2023_, 5, v_cache_2012_);
lean_ctor_set(v_reuseFailAlloc_2023_, 6, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2023_, 7, v_infoState_2014_);
lean_ctor_set(v_reuseFailAlloc_2023_, 8, v_snapshotTasks_2015_);
v___x_2021_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_st_ref_put(v___y_2002_, v___x_2021_);
goto v___jp_1989_;
}
}
}
v___jp_2027_:
{
lean_object* v___x_2034_; lean_object* v_toCold_2035_; lean_object* v_env_2036_; uint8_t v_suppressElabErrors_2037_; lean_object* v_fileName_2038_; lean_object* v_options_2039_; lean_object* v_currNamespace_2040_; lean_object* v_openDecls_2041_; lean_object* v_ictx_2042_; lean_object* v_pmctx_2043_; lean_object* v_blockCtxt_2044_; lean_object* v___x_2045_; lean_object* v_s_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_s_2049_; lean_object* v_errors_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2034_ = lean_st_ref_get(v___y_2032_);
v_toCold_2035_ = lean_ctor_get(v___y_2028_, 0);
v_env_2036_ = lean_ctor_get(v___x_2034_, 0);
lean_inc_ref_n(v_env_2036_, 2);
lean_dec(v___x_2034_);
v_suppressElabErrors_2037_ = lean_ctor_get_uint8(v___y_2028_, sizeof(void*)*3 + 1);
v_fileName_2038_ = lean_ctor_get(v_toCold_2035_, 0);
v_options_2039_ = lean_ctor_get(v_toCold_2035_, 2);
v_currNamespace_2040_ = lean_ctor_get(v_toCold_2035_, 4);
v_openDecls_2041_ = lean_ctor_get(v_toCold_2035_, 5);
lean_inc(v___y_2033_);
lean_inc_ref_n(v_fileMap_2026_, 2);
lean_inc_ref(v_fileName_2038_);
lean_inc_ref(v___y_2031_);
v_ictx_2042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_2042_, 0, v___y_2031_);
lean_ctor_set(v_ictx_2042_, 1, v_fileName_2038_);
lean_ctor_set(v_ictx_2042_, 2, v_fileMap_2026_);
lean_ctor_set(v_ictx_2042_, 3, v___y_2033_);
lean_inc(v_openDecls_2041_);
lean_inc(v_currNamespace_2040_);
lean_inc_ref(v_options_2039_);
v_pmctx_2043_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_2043_, 0, v_env_2036_);
lean_ctor_set(v_pmctx_2043_, 1, v_options_2039_);
lean_ctor_set(v_pmctx_2043_, 2, v_currNamespace_2040_);
lean_ctor_set(v_pmctx_2043_, 3, v_openDecls_2041_);
lean_inc(v___y_2029_);
v_blockCtxt_2044_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_fileMap_2026_, v___y_2030_, v___y_2029_, v___y_2033_);
lean_dec(v___y_2030_);
v___x_2045_ = l_Lean_Parser_mkParserState(v___y_2031_);
v_s_2046_ = l_Lean_Parser_ParserState_setPos(v___x_2045_, v___y_2029_);
lean_inc_ref(v_blockCtxt_2044_);
v___x_2047_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_2047_, 0, v_blockCtxt_2044_);
v___x_2048_ = l_Lean_Parser_getTokenTable(v_env_2036_);
lean_inc_ref(v___x_2048_);
lean_inc_ref(v_pmctx_2043_);
lean_inc_ref_n(v_ictx_2042_, 2);
v_s_2049_ = l_Lean_Parser_ParserFn_run(v___x_2047_, v_ictx_2042_, v_pmctx_2043_, v___x_2048_, v_s_2046_);
lean_inc_ref(v_s_2049_);
v_errors_2050_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v_ictx_2042_, v_pmctx_2043_, v___x_2048_, v___y_2031_, v_blockCtxt_2044_, v_s_2049_);
v___x_2051_ = lean_array_get_size(v_errors_2050_);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_nat_dec_eq(v___x_2051_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; size_t v_sz_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v_s_2049_);
lean_dec_ref(v___y_2031_);
v___x_2054_ = lean_box(0);
v_sz_2055_ = lean_array_size(v_errors_2050_);
v___x_2056_ = ((size_t)0ULL);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v_ictx_2042_, v___x_2051_, v_errors_2050_, v_sz_2055_, v___x_2056_, v___x_2054_, v___y_2028_, v___y_2032_);
lean_dec_ref(v_errors_2050_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2065_; 
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v___x_2057_, 0);
lean_dec(v_unused_2066_);
v___x_2059_ = v___x_2057_;
v_isShared_2060_ = v_isSharedCheck_2065_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v___x_2057_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2065_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = lean_box(0);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2061_);
v___x_2063_ = v___x_2059_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2057_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2057_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_stxStack_2075_; lean_object* v_pos_2076_; uint8_t v___x_2077_; 
lean_dec_ref(v_errors_2050_);
v_stxStack_2075_ = lean_ctor_get(v_s_2049_, 0);
lean_inc_ref(v_stxStack_2075_);
v_pos_2076_ = lean_ctor_get(v_s_2049_, 2);
lean_inc(v_pos_2076_);
lean_dec_ref(v_s_2049_);
v___x_2077_ = l_Lean_Parser_InputContext_atEnd(v_ictx_2042_, v_pos_2076_);
lean_dec_ref_known(v_ictx_2042_, 4);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint32_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref(v_stxStack_2075_);
lean_inc_ref(v_fileMap_2026_);
v___x_2078_ = l_Lean_FileMap_toPosition(v_fileMap_2026_, v_pos_2076_);
v___x_2079_ = lean_box(0);
v___x_2080_ = 2;
v___x_2081_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_2082_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__0));
v___x_2083_ = lean_string_utf8_get(v___y_2031_, v_pos_2076_);
lean_dec(v_pos_2076_);
lean_dec_ref(v___y_2031_);
v___x_2084_ = lean_string_push(v___x_2081_, v___x_2083_);
v___x_2085_ = lean_string_append(v___x_2082_, v___x_2084_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__4___closed__1));
v___x_2087_ = lean_string_append(v___x_2085_, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
v___x_2089_ = l_Lean_MessageData_ofFormat(v___x_2088_);
if (v_suppressElabErrors_2037_ == 0)
{
v___y_1993_ = v___x_2080_;
v___y_1994_ = v___x_2077_;
v___y_1995_ = v___x_2081_;
v___y_1996_ = v___x_2078_;
v___y_1997_ = v___x_2089_;
v___y_1998_ = v___x_2079_;
v___y_1999_ = v_fileName_2038_;
v_currNamespace_2000_ = v_currNamespace_2040_;
v_openDecls_2001_ = v_openDecls_2041_;
v___y_2002_ = v___y_2032_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; uint8_t v___x_2093_; 
v___x_2090_ = lean_box(v_suppressElabErrors_2037_);
v___x_2091_ = lean_box(v___x_2077_);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2092_, 0, v___x_2090_);
lean_closure_set(v___f_2092_, 1, v___x_2091_);
lean_inc_ref(v___x_2089_);
v___x_2093_ = l_Lean_MessageData_hasTag(v___f_2092_, v___x_2089_);
if (v___x_2093_ == 0)
{
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2078_);
goto v___jp_1989_;
}
else
{
v___y_1993_ = v___x_2080_;
v___y_1994_ = v___x_2077_;
v___y_1995_ = v___x_2081_;
v___y_1996_ = v___x_2078_;
v___y_1997_ = v___x_2089_;
v___y_1998_ = v___x_2079_;
v___y_1999_ = v_fileName_2038_;
v_currNamespace_2000_ = v_currNamespace_2040_;
v_openDecls_2001_ = v_openDecls_2041_;
v___y_2002_ = v___y_2032_;
goto v___jp_1992_;
}
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec(v_pos_2076_);
lean_dec_ref(v___y_2031_);
v___x_2094_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2075_);
lean_dec_ref(v_stxStack_2075_);
v___x_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
return v___x_2096_;
}
}
}
v___jp_2097_:
{
lean_object* v_snd_2101_; lean_object* v_fst_2102_; lean_object* v_fst_2103_; lean_object* v_snd_2104_; lean_object* v_source_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v_snd_2101_ = lean_ctor_get(v_____x_2098_, 1);
lean_inc(v_snd_2101_);
v_fst_2102_ = lean_ctor_get(v_____x_2098_, 0);
lean_inc(v_fst_2102_);
lean_dec_ref(v_____x_2098_);
v_fst_2103_ = lean_ctor_get(v_snd_2101_, 0);
lean_inc(v_fst_2103_);
v_snd_2104_ = lean_ctor_get(v_snd_2101_, 1);
lean_inc(v_snd_2104_);
lean_dec(v_snd_2101_);
v_source_2105_ = lean_ctor_get(v_fileMap_2026_, 0);
v___x_2106_ = lean_string_utf8_byte_size(v_source_2105_);
v___x_2107_ = lean_nat_dec_le(v_snd_2104_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_dec(v_snd_2104_);
lean_inc_ref(v_source_2105_);
v___y_2028_ = v___y_2099_;
v___y_2029_ = v_fst_2103_;
v___y_2030_ = v_fst_2102_;
v___y_2031_ = v_source_2105_;
v___y_2032_ = v___y_2100_;
v___y_2033_ = v___x_2106_;
goto v___jp_2027_;
}
else
{
lean_inc_ref(v_source_2105_);
v___y_2028_ = v___y_2099_;
v___y_2029_ = v_fst_2103_;
v___y_2030_ = v_fst_2102_;
v___y_2031_ = v_source_2105_;
v___y_2032_ = v___y_2100_;
v___y_2033_ = v_snd_2104_;
goto v___jp_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v_docComment_2120_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_2138_, lean_object* v_binders_2139_, lean_object* v_docComment_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_2140_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; lean_object* v_body_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
lean_dec_ref_known(v___x_2148_, 1);
v___x_2149_ = lean_unsigned_to_nat(1u);
v_body_2150_ = l_Lean_Syntax_getArg(v_docComment_2140_, v___x_2149_);
v___x_2151_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
v___x_2152_ = l_Lean_Syntax_isOfKind(v_body_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = l_Lean_TSyntax_getDocString(v_docComment_2140_);
v___x_2154_ = l_Lean_versoDocStringOfText(v_declName_2138_, v_binders_2139_, v___x_2153_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
return v___x_2154_;
}
else
{
lean_object* v___x_2155_; lean_object* v_markup_2156_; 
v___x_2155_ = l_Lean_VersoDocstringView_of(v_docComment_2140_);
v_markup_2156_ = lean_ctor_get(v___x_2155_, 1);
lean_inc_ref(v_markup_2156_);
lean_dec_ref(v___x_2155_);
if (lean_obj_tag(v_markup_2156_) == 0)
{
lean_object* v_doc_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_doc_2157_ = lean_ctor_get(v_markup_2156_, 0);
lean_inc(v_doc_2157_);
lean_dec_ref_known(v_markup_2156_, 1);
v___x_2158_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2157_);
lean_dec(v_doc_2157_);
v___x_2159_ = lean_box(0);
v___x_2160_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_2138_, v_binders_2139_, v___x_2158_, v___x_2159_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
return v___x_2160_;
}
else
{
lean_object* v_text_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_text_2161_ = lean_ctor_get(v_markup_2156_, 0);
lean_inc(v_text_2161_);
lean_dec_ref_known(v_markup_2156_, 1);
v___x_2162_ = l_Lean_Syntax_getAtomVal(v_text_2161_);
lean_dec(v_text_2161_);
v___x_2163_ = l_Lean_versoDocStringOfText(v_declName_2138_, v_binders_2139_, v___x_2162_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
return v___x_2163_;
}
}
}
else
{
lean_object* v___x_2164_; 
lean_dec_ref_known(v___x_2148_, 1);
v___x_2164_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2212_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2212_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2212_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
if (lean_obj_tag(v_a_2165_) == 1)
{
lean_object* v_val_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; 
lean_del_object(v___x_2167_);
v_val_2169_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_val_2169_);
lean_dec_ref_known(v_a_2165_, 1);
v___x_2170_ = l_Lean_TSyntax_getVersoBlocks(v_val_2169_);
lean_dec(v_val_2169_);
v___x_2171_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2171_, 0, v___x_2170_);
v___x_2172_ = 0;
v___x_2173_ = l_Lean_Doc_DocM_exec___redArg(v_declName_2138_, v_binders_2139_, v___x_2171_, v___x_2172_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2199_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2199_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2199_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2198_; 
v_fst_2178_ = lean_ctor_get(v_a_2174_, 0);
v_snd_2179_ = lean_ctor_get(v_a_2174_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_2174_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2181_ = v_a_2174_;
v_isShared_2182_ = v_isSharedCheck_2198_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_inc(v_fst_2178_);
lean_dec(v_a_2174_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2198_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_fst_2183_; lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2197_; 
v_fst_2183_ = lean_ctor_get(v_fst_2178_, 0);
v_snd_2184_ = lean_ctor_get(v_fst_2178_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_fst_2178_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2186_ = v_fst_2178_;
v_isShared_2187_ = v_isSharedCheck_2197_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_inc(v_fst_2183_);
lean_dec(v_fst_2178_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2197_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_fst_2183_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_snd_2184_);
v___x_2189_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2189_);
v___x_2191_ = v___x_2181_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_snd_2179_);
v___x_2191_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2191_);
v___x_2193_ = v___x_2176_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_a_2200_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2173_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2173_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec(v_a_2165_);
lean_dec(v_binders_2139_);
lean_dec(v_declName_2138_);
v___x_2208_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2208_);
v___x_2210_ = v___x_2167_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_binders_2139_);
lean_dec(v_declName_2138_);
v_a_2213_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2164_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2164_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_2221_, lean_object* v_binders_2222_, lean_object* v_docComment_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_versoDocString(v_declName_2221_, v_binders_2222_, v_docComment_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_docComment_2223_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v_ictx_2232_, lean_object* v___x_2233_, lean_object* v_as_2234_, size_t v_sz_2235_, size_t v_i_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v_ictx_2232_, v___x_2233_, v_as_2234_, v_sz_2235_, v_i_2236_, v_b_2237_, v___y_2242_, v___y_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v_ictx_2246_, lean_object* v___x_2247_, lean_object* v_as_2248_, lean_object* v_sz_2249_, lean_object* v_i_2250_, lean_object* v_b_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
size_t v_sz_boxed_2259_; size_t v_i_boxed_2260_; lean_object* v_res_2261_; 
v_sz_boxed_2259_ = lean_unbox_usize(v_sz_2249_);
lean_dec(v_sz_2249_);
v_i_boxed_2260_ = lean_unbox_usize(v_i_2250_);
lean_dec(v_i_2250_);
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v_ictx_2246_, v___x_2247_, v_as_2248_, v_sz_boxed_2259_, v_i_boxed_2260_, v_b_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec_ref(v_as_2248_);
lean_dec(v___x_2247_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_2262_, lean_object* v_msg_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_msg_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2272_, lean_object* v_msg_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_2272_, v_msg_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_msgData_2282_, lean_object* v_macroStack_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msgData_2282_, v_macroStack_2283_, v___y_2288_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2292_, lean_object* v_macroStack_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_msgData_2292_, v_macroStack_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_2302_, lean_object* v_doc_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2311_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v_val_2319_; lean_object* v_env_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2311_ = lean_st_ref_get(v_a_2309_);
v_env_2321_ = lean_ctor_get(v___x_2311_, 0);
lean_inc_ref(v_env_2321_);
lean_dec(v___x_2311_);
v___x_2322_ = l_Lean_getMainVersoModuleDocs(v_env_2321_);
v___x_2323_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_2322_);
lean_dec_ref(v___x_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2303_);
v___x_2325_ = lean_unsigned_to_nat(0u);
v___y_2313_ = v___x_2324_;
v___y_2314_ = v___x_2325_;
goto v___jp_2312_;
}
else
{
lean_object* v_val_2326_; 
v_val_2326_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_val_2326_);
lean_dec_ref_known(v___x_2323_, 1);
v_val_2319_ = v_val_2326_;
goto v___jp_2318_;
}
}
else
{
lean_object* v_val_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_val_2327_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_nat_add(v_val_2327_, v___x_2328_);
lean_dec(v_val_2327_);
v_val_2319_ = v___x_2329_;
goto v___jp_2318_;
}
v___jp_2312_:
{
lean_object* v___x_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_2315_, 0, v_range_2302_);
lean_closure_set(v___x_2315_, 1, v___y_2313_);
lean_closure_set(v___x_2315_, 2, v___y_2314_);
v___x_2316_ = 0;
v___x_2317_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_2315_, v___x_2316_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2317_;
}
v___jp_2318_:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2303_);
v___y_2313_ = v___x_2320_;
v___y_2314_ = v_val_2319_;
goto v___jp_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_2330_, lean_object* v_doc_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_versoModDocString(v_range_2330_, v_doc_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_doc_2331_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2349_, lean_object* v_docComment_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_2359_ = l_Lean_versoDocStringOfText(v_declName_2349_, v___x_2358_, v_docComment_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2360_, lean_object* v_docComment_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_versoDocStringFromString(v_declName_2360_, v_docComment_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2370_, lean_object* v_declName_2371_, lean_object* v_env_2372_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = l_Lean_docStringExt;
v___x_2374_ = l_String_removeLeadingSpaces(v_docString_2370_);
v___x_2375_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2373_, v_env_2372_, v_declName_2371_, v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2376_, lean_object* v_modifyEnv_2377_, lean_object* v_docString_2378_){
_start:
{
lean_object* v___f_2379_; lean_object* v___x_2380_; 
v___f_2379_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2379_, 0, v_docString_2378_);
lean_closure_set(v___f_2379_, 1, v_declName_2376_);
v___x_2380_ = lean_apply_1(v_modifyEnv_2377_, v___f_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_docComment_2383_, lean_object* v_toBind_2384_, lean_object* v___f_2385_, lean_object* v_____r_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = l_Lean_getDocStringText___redArg(v_inst_2381_, v_inst_2382_, v_docComment_2383_);
v___x_2388_ = lean_apply_4(v_toBind_2384_, lean_box(0), lean_box(0), v___x_2387_, v___f_2385_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2389_, lean_object* v_inst_2390_, lean_object* v_inst_2391_, lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_docComment_2394_, lean_object* v_toBind_2395_, lean_object* v___f_2396_, lean_object* v_____r_2397_){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = l_Lean_validateDocComment___redArg(v_inst_2389_, v_inst_2390_, v_inst_2391_, v_inst_2392_, v_inst_2393_, v_docComment_2394_);
v___x_2399_ = lean_apply_4(v_toBind_2395_, lean_box(0), lean_box(0), v___x_2398_, v___f_2396_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_inst_2403_, lean_object* v_inst_2404_, lean_object* v_docComment_2405_, lean_object* v_toBind_2406_, lean_object* v___f_2407_, lean_object* v_____r_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2400_, v_inst_2401_, v_inst_2402_, v_inst_2403_, v_inst_2404_, v_docComment_2405_, v_toBind_2406_, v___f_2407_, v_____r_2408_);
lean_dec(v_docComment_2405_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2410_, lean_object* v_____r_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_apply_1(v___f_2410_, v_____r_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
return v___x_2415_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2419_, lean_object* v_declName_2420_, uint8_t v___x_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_toBind_2424_, lean_object* v___f_2425_, lean_object* v_____do__lift_2426_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2426_, v_declName_2420_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_dec(v___f_2425_);
lean_dec(v_toBind_2424_);
lean_dec_ref(v_inst_2423_);
lean_dec_ref(v_inst_2422_);
lean_dec(v_declName_2420_);
goto v___jp_2427_;
}
else
{
lean_dec_ref_known(v___x_2430_, 1);
if (v___x_2421_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec(v___f_2419_);
v___x_2431_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2432_ = l_Lean_MessageData_ofConstName(v_declName_2420_, v___x_2421_);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = l_Lean_throwError___redArg(v_inst_2422_, v_inst_2423_, v___x_2435_);
v___x_2437_ = lean_apply_4(v_toBind_2424_, lean_box(0), lean_box(0), v___x_2436_, v___f_2425_);
return v___x_2437_;
}
else
{
lean_dec(v___f_2425_);
lean_dec(v_toBind_2424_);
lean_dec_ref(v_inst_2423_);
lean_dec_ref(v_inst_2422_);
lean_dec(v_declName_2420_);
goto v___jp_2427_;
}
}
v___jp_2427_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_box(0);
v___x_2429_ = lean_apply_1(v___f_2419_, v___x_2428_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2438_, lean_object* v_declName_2439_, lean_object* v___x_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_toBind_2443_, lean_object* v___f_2444_, lean_object* v_____do__lift_2445_){
_start:
{
uint8_t v___x_247__boxed_2446_; lean_object* v_res_2447_; 
v___x_247__boxed_2446_ = lean_unbox(v___x_2440_);
v_res_2447_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2438_, v_declName_2439_, v___x_247__boxed_2446_, v_inst_2441_, v_inst_2442_, v_toBind_2443_, v___f_2444_, v_____do__lift_2445_);
lean_dec_ref(v_____do__lift_2445_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_declName_2455_, lean_object* v_docComment_2456_){
_start:
{
lean_object* v_toApplicative_2457_; lean_object* v_toBind_2458_; lean_object* v_toPure_2459_; uint8_t v___x_2460_; 
v_toApplicative_2457_ = lean_ctor_get(v_inst_2448_, 0);
v_toBind_2458_ = lean_ctor_get(v_inst_2448_, 1);
lean_inc(v_toBind_2458_);
v_toPure_2459_ = lean_ctor_get(v_toApplicative_2457_, 1);
v___x_2460_ = l_Lean_Name_isAnonymous(v_declName_2455_);
if (v___x_2460_ == 0)
{
lean_object* v_getEnv_2461_; lean_object* v_modifyEnv_2462_; lean_object* v___f_2463_; lean_object* v___f_2464_; lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___x_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; 
v_getEnv_2461_ = lean_ctor_get(v_inst_2451_, 0);
lean_inc(v_getEnv_2461_);
v_modifyEnv_2462_ = lean_ctor_get(v_inst_2451_, 1);
lean_inc(v_modifyEnv_2462_);
lean_dec_ref(v_inst_2451_);
lean_inc(v_declName_2455_);
v___f_2463_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2463_, 0, v_declName_2455_);
lean_closure_set(v___f_2463_, 1, v_modifyEnv_2462_);
lean_inc_n(v_toBind_2458_, 3);
lean_inc(v_docComment_2456_);
lean_inc_ref(v_inst_2452_);
lean_inc_ref_n(v_inst_2448_, 2);
v___f_2464_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2464_, 0, v_inst_2448_);
lean_closure_set(v___f_2464_, 1, v_inst_2452_);
lean_closure_set(v___f_2464_, 2, v_docComment_2456_);
lean_closure_set(v___f_2464_, 3, v_toBind_2458_);
lean_closure_set(v___f_2464_, 4, v___f_2463_);
v___f_2465_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2465_, 0, v_inst_2448_);
lean_closure_set(v___f_2465_, 1, v_inst_2449_);
lean_closure_set(v___f_2465_, 2, v_inst_2453_);
lean_closure_set(v___f_2465_, 3, v_inst_2454_);
lean_closure_set(v___f_2465_, 4, v_inst_2450_);
lean_closure_set(v___f_2465_, 5, v_docComment_2456_);
lean_closure_set(v___f_2465_, 6, v_toBind_2458_);
lean_closure_set(v___f_2465_, 7, v___f_2464_);
lean_inc_ref(v___f_2465_);
v___f_2466_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2466_, 0, v___f_2465_);
v___x_2467_ = lean_box(v___x_2460_);
v___f_2468_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2468_, 0, v___f_2465_);
lean_closure_set(v___f_2468_, 1, v_declName_2455_);
lean_closure_set(v___f_2468_, 2, v___x_2467_);
lean_closure_set(v___f_2468_, 3, v_inst_2448_);
lean_closure_set(v___f_2468_, 4, v_inst_2452_);
lean_closure_set(v___f_2468_, 5, v_toBind_2458_);
lean_closure_set(v___f_2468_, 6, v___f_2466_);
v___x_2469_ = lean_apply_4(v_toBind_2458_, lean_box(0), lean_box(0), v_getEnv_2461_, v___f_2468_);
return v___x_2469_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_inc(v_toPure_2459_);
lean_dec(v_toBind_2458_);
lean_dec(v_docComment_2456_);
lean_dec(v_declName_2455_);
lean_dec(v_inst_2454_);
lean_dec_ref(v_inst_2453_);
lean_dec_ref(v_inst_2452_);
lean_dec_ref(v_inst_2451_);
lean_dec(v_inst_2450_);
lean_dec(v_inst_2449_);
lean_dec_ref(v_inst_2448_);
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_apply_2(v_toPure_2459_, lean_box(0), v___x_2470_);
return v___x_2471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2472_, lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_declName_2480_, lean_object* v_docComment_2481_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_addMarkdownDocString___redArg(v_inst_2473_, v_inst_2474_, v_inst_2475_, v_inst_2476_, v_inst_2477_, v_inst_2478_, v_inst_2479_, v_declName_2480_, v_docComment_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2483_, lean_object* v_x1_2484_, lean_object* v_x2_2485_){
_start:
{
lean_object* v_index_2486_; lean_object* v_sourceString_2487_; lean_object* v_imports_2488_; lean_object* v_currNamespace_2489_; lean_object* v_openDecls_2490_; lean_object* v_options_2491_; lean_object* v_check_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2505_; 
v_index_2486_ = lean_ctor_get(v_x2_2485_, 1);
v_sourceString_2487_ = lean_ctor_get(v_x2_2485_, 2);
v_imports_2488_ = lean_ctor_get(v_x2_2485_, 3);
v_currNamespace_2489_ = lean_ctor_get(v_x2_2485_, 4);
v_openDecls_2490_ = lean_ctor_get(v_x2_2485_, 5);
v_options_2491_ = lean_ctor_get(v_x2_2485_, 6);
v_check_2492_ = lean_ctor_get(v_x2_2485_, 7);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_x2_2485_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v_x2_2485_, 0);
lean_dec(v_unused_2506_);
v___x_2494_ = v_x2_2485_;
v_isShared_2495_ = v_isSharedCheck_2505_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_check_2492_);
lean_inc(v_options_2491_);
lean_inc(v_openDecls_2490_);
lean_inc(v_currNamespace_2489_);
lean_inc(v_imports_2488_);
lean_inc(v_sourceString_2487_);
lean_inc(v_index_2486_);
lean_dec(v_x2_2485_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2505_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v_toEnvExtension_2497_; lean_object* v_asyncMode_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2496_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2497_ = lean_ctor_get(v___x_2496_, 0);
v_asyncMode_2498_ = lean_ctor_get(v_toEnvExtension_2497_, 2);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_declName_2483_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2499_);
v___x_2501_ = v___x_2494_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_index_2486_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v_sourceString_2487_);
lean_ctor_set(v_reuseFailAlloc_2504_, 3, v_imports_2488_);
lean_ctor_set(v_reuseFailAlloc_2504_, 4, v_currNamespace_2489_);
lean_ctor_set(v_reuseFailAlloc_2504_, 5, v_openDecls_2490_);
lean_ctor_set(v_reuseFailAlloc_2504_, 6, v_options_2491_);
lean_ctor_set(v_reuseFailAlloc_2504_, 7, v_check_2492_);
v___x_2501_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_box(0);
v___x_2503_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2496_, v_x1_2484_, v___x_2501_, v_asyncMode_2498_, v___x_2502_);
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_2526_, lean_object* v_docs_2527_, lean_object* v_deferred_2528_, lean_object* v___f_2529_, lean_object* v_env_2530_){
_start:
{
lean_object* v___x_2531_; lean_object* v_env_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2531_ = l_Lean_versoDocStringExt;
v_env_2532_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2531_, v_env_2530_, v_declName_2526_, v_docs_2527_);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_array_get_size(v_deferred_2528_);
v___x_2535_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2536_ = lean_nat_dec_lt(v___x_2533_, v___x_2534_);
if (v___x_2536_ == 0)
{
lean_dec_ref(v___f_2529_);
lean_dec_ref(v_deferred_2528_);
return v_env_2532_;
}
else
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_nat_dec_le(v___x_2534_, v___x_2534_);
if (v___x_2537_ == 0)
{
if (v___x_2536_ == 0)
{
lean_dec_ref(v___f_2529_);
lean_dec_ref(v_deferred_2528_);
return v_env_2532_;
}
else
{
size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = lean_usize_of_nat(v___x_2534_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2535_, v___f_2529_, v_deferred_2528_, v___x_2538_, v___x_2539_, v_env_2532_);
return v___x_2540_;
}
}
else
{
size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = lean_usize_of_nat(v___x_2534_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2535_, v___f_2529_, v_deferred_2528_, v___x_2541_, v___x_2542_, v_env_2532_);
return v___x_2543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_2544_, lean_object* v___f_2545_, lean_object* v_____r_2546_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_apply_1(v_modifyEnv_2544_, v___f_2545_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_2550_, lean_object* v_modifyEnv_2551_, lean_object* v___f_2552_, uint8_t v___x_2553_, lean_object* v_inst_2554_, lean_object* v_inst_2555_, lean_object* v_toBind_2556_, lean_object* v___f_2557_, lean_object* v_____do__lift_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2558_, v_declName_2550_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2560_; 
lean_dec(v___f_2557_);
lean_dec(v_toBind_2556_);
lean_dec_ref(v_inst_2555_);
lean_dec_ref(v_inst_2554_);
lean_dec(v_declName_2550_);
v___x_2560_ = lean_apply_1(v_modifyEnv_2551_, v___f_2552_);
return v___x_2560_;
}
else
{
lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2577_; 
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2559_, 0);
lean_dec(v_unused_2578_);
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2577_;
goto v_resetjp_2561_;
}
else
{
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2577_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
if (v___x_2553_ == 0)
{
lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
lean_dec_ref(v___f_2552_);
lean_dec(v_modifyEnv_2551_);
v___x_2564_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2565_ = 1;
v___x_2566_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2550_, v___x_2565_);
v___x_2567_ = lean_string_append(v___x_2564_, v___x_2566_);
lean_dec_ref(v___x_2566_);
v___x_2568_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2569_ = lean_string_append(v___x_2567_, v___x_2568_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 3);
lean_ctor_set(v___x_2562_, 0, v___x_2569_);
v___x_2571_ = v___x_2562_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = l_Lean_MessageData_ofFormat(v___x_2571_);
v___x_2573_ = l_Lean_throwError___redArg(v_inst_2554_, v_inst_2555_, v___x_2572_);
v___x_2574_ = lean_apply_4(v_toBind_2556_, lean_box(0), lean_box(0), v___x_2573_, v___f_2557_);
return v___x_2574_;
}
}
else
{
lean_object* v___x_2576_; 
lean_del_object(v___x_2562_);
lean_dec(v___f_2557_);
lean_dec(v_toBind_2556_);
lean_dec_ref(v_inst_2555_);
lean_dec_ref(v_inst_2554_);
lean_dec(v_declName_2550_);
v___x_2576_ = lean_apply_1(v_modifyEnv_2551_, v___f_2552_);
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_2579_, lean_object* v_modifyEnv_2580_, lean_object* v___f_2581_, lean_object* v___x_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_toBind_2585_, lean_object* v___f_2586_, lean_object* v_____do__lift_2587_){
_start:
{
uint8_t v___x_374__boxed_2588_; lean_object* v_res_2589_; 
v___x_374__boxed_2588_ = lean_unbox(v___x_2582_);
v_res_2589_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_2579_, v_modifyEnv_2580_, v___f_2581_, v___x_374__boxed_2588_, v_inst_2583_, v_inst_2584_, v_toBind_2585_, v___f_2586_, v_____do__lift_2587_);
lean_dec_ref(v_____do__lift_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_declName_2593_, lean_object* v_docs_2594_, lean_object* v_deferred_2595_){
_start:
{
lean_object* v_toApplicative_2596_; lean_object* v_toBind_2597_; lean_object* v_toPure_2598_; uint8_t v___x_2599_; 
v_toApplicative_2596_ = lean_ctor_get(v_inst_2590_, 0);
v_toBind_2597_ = lean_ctor_get(v_inst_2590_, 1);
lean_inc(v_toBind_2597_);
v_toPure_2598_ = lean_ctor_get(v_toApplicative_2596_, 1);
v___x_2599_ = l_Lean_Name_isAnonymous(v_declName_2593_);
if (v___x_2599_ == 0)
{
lean_object* v_getEnv_2600_; lean_object* v_modifyEnv_2601_; lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; 
v_getEnv_2600_ = lean_ctor_get(v_inst_2591_, 0);
lean_inc(v_getEnv_2600_);
v_modifyEnv_2601_ = lean_ctor_get(v_inst_2591_, 1);
lean_inc_n(v_modifyEnv_2601_, 2);
lean_dec_ref(v_inst_2591_);
lean_inc_n(v_declName_2593_, 2);
v___f_2602_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2602_, 0, v_declName_2593_);
v___f_2603_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2603_, 0, v_declName_2593_);
lean_closure_set(v___f_2603_, 1, v_docs_2594_);
lean_closure_set(v___f_2603_, 2, v_deferred_2595_);
lean_closure_set(v___f_2603_, 3, v___f_2602_);
lean_inc_ref(v___f_2603_);
v___f_2604_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2604_, 0, v_modifyEnv_2601_);
lean_closure_set(v___f_2604_, 1, v___f_2603_);
v___x_2605_ = lean_box(v___x_2599_);
lean_inc(v_toBind_2597_);
v___f_2606_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2606_, 0, v_declName_2593_);
lean_closure_set(v___f_2606_, 1, v_modifyEnv_2601_);
lean_closure_set(v___f_2606_, 2, v___f_2603_);
lean_closure_set(v___f_2606_, 3, v___x_2605_);
lean_closure_set(v___f_2606_, 4, v_inst_2590_);
lean_closure_set(v___f_2606_, 5, v_inst_2592_);
lean_closure_set(v___f_2606_, 6, v_toBind_2597_);
lean_closure_set(v___f_2606_, 7, v___f_2604_);
v___x_2607_ = lean_apply_4(v_toBind_2597_, lean_box(0), lean_box(0), v_getEnv_2600_, v___f_2606_);
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_inc(v_toPure_2598_);
lean_dec(v_toBind_2597_);
lean_dec_ref(v_deferred_2595_);
lean_dec_ref(v_docs_2594_);
lean_dec(v_declName_2593_);
lean_dec_ref(v_inst_2592_);
lean_dec_ref(v_inst_2591_);
lean_dec_ref(v_inst_2590_);
v___x_2608_ = lean_box(0);
v___x_2609_ = lean_apply_2(v_toPure_2598_, lean_box(0), v___x_2608_);
return v___x_2609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_declName_2615_, lean_object* v_docs_2616_, lean_object* v_deferred_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2611_, v_inst_2612_, v_inst_2614_, v_declName_2615_, v_docs_2616_, v_deferred_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_declName_2624_, lean_object* v_docs_2625_, lean_object* v_deferred_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_addVersoDocStringCore(v_m_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v_inst_2623_, v_declName_2624_, v_docs_2625_, v_deferred_2626_);
lean_dec(v_inst_2622_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_2628_, lean_object* v_x1_2629_, lean_object* v_x2_2630_){
_start:
{
lean_object* v_index_2631_; lean_object* v_sourceString_2632_; lean_object* v_imports_2633_; lean_object* v_currNamespace_2634_; lean_object* v_openDecls_2635_; lean_object* v_options_2636_; lean_object* v_check_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2650_; 
v_index_2631_ = lean_ctor_get(v_x2_2630_, 1);
v_sourceString_2632_ = lean_ctor_get(v_x2_2630_, 2);
v_imports_2633_ = lean_ctor_get(v_x2_2630_, 3);
v_currNamespace_2634_ = lean_ctor_get(v_x2_2630_, 4);
v_openDecls_2635_ = lean_ctor_get(v_x2_2630_, 5);
v_options_2636_ = lean_ctor_get(v_x2_2630_, 6);
v_check_2637_ = lean_ctor_get(v_x2_2630_, 7);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_x2_2630_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v_x2_2630_, 0);
lean_dec(v_unused_2651_);
v___x_2639_ = v_x2_2630_;
v_isShared_2640_ = v_isSharedCheck_2650_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_check_2637_);
lean_inc(v_options_2636_);
lean_inc(v_openDecls_2635_);
lean_inc(v_currNamespace_2634_);
lean_inc(v_imports_2633_);
lean_inc(v_sourceString_2632_);
lean_inc(v_index_2631_);
lean_dec(v_x2_2630_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2650_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v_toEnvExtension_2642_; lean_object* v_asyncMode_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2641_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2642_ = lean_ctor_get(v___x_2641_, 0);
v_asyncMode_2643_ = lean_ctor_get(v_toEnvExtension_2642_, 2);
v___x_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_size_2628_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2644_);
v___x_2646_ = v___x_2639_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_index_2631_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_sourceString_2632_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_imports_2633_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_currNamespace_2634_);
lean_ctor_set(v_reuseFailAlloc_2649_, 5, v_openDecls_2635_);
lean_ctor_set(v_reuseFailAlloc_2649_, 6, v_options_2636_);
lean_ctor_set(v_reuseFailAlloc_2649_, 7, v_check_2637_);
v___x_2646_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_box(0);
v___x_2648_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2641_, v_x1_2629_, v___x_2646_, v_asyncMode_2643_, v___x_2647_);
return v___x_2648_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_deferred_2658_, lean_object* v_inst_2659_, lean_object* v___f_2660_, lean_object* v_____do__lift_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2661_, v_docs_2655_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_dec_ref(v___f_2660_);
lean_dec_ref(v_inst_2659_);
lean_dec_ref(v_deferred_2658_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2664_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2665_ = l_Lean_stringToMessageData(v_a_2663_);
v___x_2666_ = l_Lean_indentD(v___x_2665_);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2664_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = l_Lean_throwError___redArg(v_inst_2656_, v_inst_2657_, v___x_2667_);
return v___x_2668_;
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
lean_dec_ref(v_inst_2657_);
lean_dec_ref(v_inst_2656_);
v_a_2669_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2670_ = lean_unsigned_to_nat(0u);
v___x_2671_ = lean_array_get_size(v_deferred_2658_);
v___x_2672_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2673_ = lean_nat_dec_lt(v___x_2670_, v___x_2671_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; 
lean_dec_ref(v___f_2660_);
lean_dec_ref(v_deferred_2658_);
v___x_2674_ = l_Lean_setEnv___redArg(v_inst_2659_, v_a_2669_);
return v___x_2674_;
}
else
{
uint8_t v___x_2675_; 
v___x_2675_ = lean_nat_dec_le(v___x_2671_, v___x_2671_);
if (v___x_2675_ == 0)
{
if (v___x_2673_ == 0)
{
lean_object* v___x_2676_; 
lean_dec_ref(v___f_2660_);
lean_dec_ref(v_deferred_2658_);
v___x_2676_ = l_Lean_setEnv___redArg(v_inst_2659_, v_a_2669_);
return v___x_2676_;
}
else
{
size_t v___x_2677_; size_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2677_ = ((size_t)0ULL);
v___x_2678_ = lean_usize_of_nat(v___x_2671_);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2672_, v___f_2660_, v_deferred_2658_, v___x_2677_, v___x_2678_, v_a_2669_);
v___x_2680_ = l_Lean_setEnv___redArg(v_inst_2659_, v___x_2679_);
return v___x_2680_;
}
}
else
{
size_t v___x_2681_; size_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2681_ = ((size_t)0ULL);
v___x_2682_ = lean_usize_of_nat(v___x_2671_);
v___x_2683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2672_, v___f_2660_, v_deferred_2658_, v___x_2681_, v___x_2682_, v_a_2669_);
v___x_2684_ = l_Lean_setEnv___redArg(v_inst_2659_, v___x_2683_);
return v___x_2684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_deferred_2688_, lean_object* v_inst_2689_, lean_object* v_toBind_2690_, lean_object* v_getEnv_2691_, lean_object* v_____do__lift_2692_){
_start:
{
lean_object* v___x_2693_; lean_object* v_size_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; 
v___x_2693_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2692_);
v_size_2694_ = lean_ctor_get(v___x_2693_, 2);
lean_inc(v_size_2694_);
lean_dec_ref(v___x_2693_);
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2695_, 0, v_size_2694_);
v___f_2696_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2696_, 0, v_docs_2685_);
lean_closure_set(v___f_2696_, 1, v_inst_2686_);
lean_closure_set(v___f_2696_, 2, v_inst_2687_);
lean_closure_set(v___f_2696_, 3, v_deferred_2688_);
lean_closure_set(v___f_2696_, 4, v_inst_2689_);
lean_closure_set(v___f_2696_, 5, v___f_2695_);
v___x_2697_ = lean_apply_4(v_toBind_2690_, lean_box(0), lean_box(0), v_getEnv_2691_, v___f_2696_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2700_ = l_Lean_stringToMessageData(v___x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_toBind_2703_, lean_object* v_getEnv_2704_, lean_object* v___f_2705_, lean_object* v_____do__lift_2706_){
_start:
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = l_Lean_getMainModuleDoc(v_____do__lift_2706_);
v___x_2708_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2707_);
lean_dec_ref(v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec(v___f_2705_);
lean_dec(v_getEnv_2704_);
lean_dec(v_toBind_2703_);
v___x_2709_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2710_ = l_Lean_throwError___redArg(v_inst_2701_, v_inst_2702_, v___x_2709_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; 
lean_dec_ref(v_inst_2702_);
lean_dec_ref(v_inst_2701_);
v___x_2711_ = lean_apply_4(v_toBind_2703_, lean_box(0), lean_box(0), v_getEnv_2704_, v___f_2705_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_docs_2715_, lean_object* v_deferred_2716_){
_start:
{
lean_object* v_toBind_2717_; lean_object* v_getEnv_2718_; lean_object* v___f_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; 
v_toBind_2717_ = lean_ctor_get(v_inst_2712_, 1);
lean_inc_n(v_toBind_2717_, 3);
v_getEnv_2718_ = lean_ctor_get(v_inst_2713_, 0);
lean_inc_n(v_getEnv_2718_, 3);
lean_inc_ref(v_inst_2714_);
lean_inc_ref(v_inst_2712_);
v___f_2719_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2719_, 0, v_docs_2715_);
lean_closure_set(v___f_2719_, 1, v_inst_2712_);
lean_closure_set(v___f_2719_, 2, v_inst_2714_);
lean_closure_set(v___f_2719_, 3, v_deferred_2716_);
lean_closure_set(v___f_2719_, 4, v_inst_2713_);
lean_closure_set(v___f_2719_, 5, v_toBind_2717_);
lean_closure_set(v___f_2719_, 6, v_getEnv_2718_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2720_, 0, v_inst_2712_);
lean_closure_set(v___f_2720_, 1, v_inst_2714_);
lean_closure_set(v___f_2720_, 2, v_toBind_2717_);
lean_closure_set(v___f_2720_, 3, v_getEnv_2718_);
lean_closure_set(v___f_2720_, 4, v___f_2719_);
v___x_2721_ = lean_apply_4(v_toBind_2717_, lean_box(0), lean_box(0), v_getEnv_2718_, v___f_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_docs_2727_, lean_object* v_deferred_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2723_, v_inst_2724_, v_inst_2726_, v_docs_2727_, v_deferred_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_docs_2735_, lean_object* v_deferred_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_addVersoModDocStringCore(v_m_2730_, v_inst_2731_, v_inst_2732_, v_inst_2733_, v_inst_2734_, v_docs_2735_, v_deferred_2736_);
lean_dec(v_inst_2733_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2738_, lean_object* v_as_2739_, size_t v_i_2740_, size_t v_stop_2741_, lean_object* v_b_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_usize_dec_eq(v_i_2740_, v_stop_2741_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v_index_2745_; lean_object* v_sourceString_2746_; lean_object* v_imports_2747_; lean_object* v_currNamespace_2748_; lean_object* v_openDecls_2749_; lean_object* v_options_2750_; lean_object* v_check_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2767_; 
v___x_2744_ = lean_array_uget(v_as_2739_, v_i_2740_);
v_index_2745_ = lean_ctor_get(v___x_2744_, 1);
v_sourceString_2746_ = lean_ctor_get(v___x_2744_, 2);
v_imports_2747_ = lean_ctor_get(v___x_2744_, 3);
v_currNamespace_2748_ = lean_ctor_get(v___x_2744_, 4);
v_openDecls_2749_ = lean_ctor_get(v___x_2744_, 5);
v_options_2750_ = lean_ctor_get(v___x_2744_, 6);
v_check_2751_ = lean_ctor_get(v___x_2744_, 7);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; 
v_unused_2768_ = lean_ctor_get(v___x_2744_, 0);
lean_dec(v_unused_2768_);
v___x_2753_ = v___x_2744_;
v_isShared_2754_ = v_isSharedCheck_2767_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_check_2751_);
lean_inc(v_options_2750_);
lean_inc(v_openDecls_2749_);
lean_inc(v_currNamespace_2748_);
lean_inc(v_imports_2747_);
lean_inc(v_sourceString_2746_);
lean_inc(v_index_2745_);
lean_dec(v___x_2744_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2767_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v_toEnvExtension_2756_; lean_object* v_asyncMode_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2755_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2756_ = lean_ctor_get(v___x_2755_, 0);
v_asyncMode_2757_ = lean_ctor_get(v_toEnvExtension_2756_, 2);
lean_inc(v_declName_2738_);
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_declName_2738_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2758_);
v___x_2760_ = v___x_2753_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_index_2745_);
lean_ctor_set(v_reuseFailAlloc_2766_, 2, v_sourceString_2746_);
lean_ctor_set(v_reuseFailAlloc_2766_, 3, v_imports_2747_);
lean_ctor_set(v_reuseFailAlloc_2766_, 4, v_currNamespace_2748_);
lean_ctor_set(v_reuseFailAlloc_2766_, 5, v_openDecls_2749_);
lean_ctor_set(v_reuseFailAlloc_2766_, 6, v_options_2750_);
lean_ctor_set(v_reuseFailAlloc_2766_, 7, v_check_2751_);
v___x_2760_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; size_t v___x_2763_; size_t v___x_2764_; 
v___x_2761_ = lean_box(0);
v___x_2762_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2755_, v_b_2742_, v___x_2760_, v_asyncMode_2757_, v___x_2761_);
v___x_2763_ = ((size_t)1ULL);
v___x_2764_ = lean_usize_add(v_i_2740_, v___x_2763_);
v_i_2740_ = v___x_2764_;
v_b_2742_ = v___x_2762_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2738_);
return v_b_2742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2769_, lean_object* v_as_2770_, lean_object* v_i_2771_, lean_object* v_stop_2772_, lean_object* v_b_2773_){
_start:
{
size_t v_i_boxed_2774_; size_t v_stop_boxed_2775_; lean_object* v_res_2776_; 
v_i_boxed_2774_ = lean_unbox_usize(v_i_2771_);
lean_dec(v_i_2771_);
v_stop_boxed_2775_ = lean_unbox_usize(v_stop_2772_);
lean_dec(v_stop_2772_);
v_res_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2769_, v_as_2770_, v_i_boxed_2774_, v_stop_boxed_2775_, v_b_2773_);
lean_dec_ref(v_as_2770_);
return v_res_2776_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2777_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
return v___x_2781_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2783_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
lean_ctor_set(v___x_2783_, 2, v___x_2782_);
lean_ctor_set(v___x_2783_, 3, v___x_2782_);
lean_ctor_set(v___x_2783_, 4, v___x_2782_);
lean_ctor_set(v___x_2783_, 5, v___x_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2784_, lean_object* v_docs_2785_, lean_object* v_deferred_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2826_; lean_object* v___y_2827_; uint8_t v___x_2845_; 
v___x_2845_ = l_Lean_Name_isAnonymous(v_declName_2784_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v_env_2847_; lean_object* v___x_2848_; 
v___x_2846_ = lean_st_ref_get(v___y_2792_);
v_env_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_ref(v_env_2847_);
lean_dec(v___x_2846_);
v___x_2848_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2847_, v_declName_2784_);
lean_dec_ref(v_env_2847_);
if (lean_obj_tag(v___x_2848_) == 0)
{
v___y_2826_ = v___y_2790_;
v___y_2827_ = v___y_2792_;
goto v___jp_2825_;
}
else
{
lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2863_; 
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; 
v_unused_2864_ = lean_ctor_get(v___x_2848_, 0);
lean_dec(v_unused_2864_);
v___x_2850_ = v___x_2848_;
v_isShared_2851_ = v_isSharedCheck_2863_;
goto v_resetjp_2849_;
}
else
{
lean_dec(v___x_2848_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2863_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
if (v___x_2845_ == 0)
{
lean_object* v___x_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_dec_ref(v_docs_2785_);
v___x_2852_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2853_ = 1;
v___x_2854_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2784_, v___x_2853_);
v___x_2855_ = lean_string_append(v___x_2852_, v___x_2854_);
lean_dec_ref(v___x_2854_);
v___x_2856_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2857_ = lean_string_append(v___x_2855_, v___x_2856_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set_tag(v___x_2850_, 3);
lean_ctor_set(v___x_2850_, 0, v___x_2857_);
v___x_2859_ = v___x_2850_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = l_Lean_MessageData_ofFormat(v___x_2859_);
v___x_2861_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_2860_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2861_;
}
}
else
{
lean_del_object(v___x_2850_);
v___y_2826_ = v___y_2790_;
v___y_2827_ = v___y_2792_;
goto v___jp_2825_;
}
}
}
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
lean_dec_ref(v_docs_2785_);
lean_dec(v_declName_2784_);
v___x_2865_ = lean_box(0);
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
v___jp_2794_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v_mctx_2809_; lean_object* v_zetaDeltaFVarIds_2810_; lean_object* v_postponed_2811_; lean_object* v_diag_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2823_; 
v___x_2805_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2806_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2806_, 0, v___y_2804_);
lean_ctor_set(v___x_2806_, 1, v___y_2803_);
lean_ctor_set(v___x_2806_, 2, v___y_2802_);
lean_ctor_set(v___x_2806_, 3, v___y_2795_);
lean_ctor_set(v___x_2806_, 4, v___y_2801_);
lean_ctor_set(v___x_2806_, 5, v___x_2805_);
lean_ctor_set(v___x_2806_, 6, v___y_2796_);
lean_ctor_set(v___x_2806_, 7, v___y_2798_);
lean_ctor_set(v___x_2806_, 8, v___y_2800_);
v___x_2807_ = lean_st_ref_put(v___y_2799_, v___x_2806_);
v___x_2808_ = lean_st_ref_take(v___y_2797_);
v_mctx_2809_ = lean_ctor_get(v___x_2808_, 0);
v_zetaDeltaFVarIds_2810_ = lean_ctor_get(v___x_2808_, 2);
v_postponed_2811_ = lean_ctor_get(v___x_2808_, 3);
v_diag_2812_ = lean_ctor_get(v___x_2808_, 4);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2808_, 1);
lean_dec(v_unused_2824_);
v___x_2814_ = v___x_2808_;
v_isShared_2815_ = v_isSharedCheck_2823_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_diag_2812_);
lean_inc(v_postponed_2811_);
lean_inc(v_zetaDeltaFVarIds_2810_);
lean_inc(v_mctx_2809_);
lean_dec(v___x_2808_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2823_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 1, v___x_2817_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_mctx_2809_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_zetaDeltaFVarIds_2810_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_postponed_2811_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_diag_2812_);
v___x_2819_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_st_ref_put(v___y_2797_, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2816_);
return v___x_2821_;
}
}
}
v___jp_2825_:
{
lean_object* v___x_2828_; lean_object* v_env_2829_; lean_object* v_nextMacroScope_2830_; lean_object* v_ngen_2831_; lean_object* v_auxDeclNGen_2832_; lean_object* v_traceState_2833_; lean_object* v_messages_2834_; lean_object* v_infoState_2835_; lean_object* v_snapshotTasks_2836_; lean_object* v___x_2837_; lean_object* v_env_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2828_ = lean_st_ref_take(v___y_2827_);
v_env_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_ref(v_env_2829_);
v_nextMacroScope_2830_ = lean_ctor_get(v___x_2828_, 1);
lean_inc(v_nextMacroScope_2830_);
v_ngen_2831_ = lean_ctor_get(v___x_2828_, 2);
lean_inc_ref(v_ngen_2831_);
v_auxDeclNGen_2832_ = lean_ctor_get(v___x_2828_, 3);
lean_inc_ref(v_auxDeclNGen_2832_);
v_traceState_2833_ = lean_ctor_get(v___x_2828_, 4);
lean_inc_ref(v_traceState_2833_);
v_messages_2834_ = lean_ctor_get(v___x_2828_, 6);
lean_inc_ref(v_messages_2834_);
v_infoState_2835_ = lean_ctor_get(v___x_2828_, 7);
lean_inc_ref(v_infoState_2835_);
v_snapshotTasks_2836_ = lean_ctor_get(v___x_2828_, 8);
lean_inc_ref(v_snapshotTasks_2836_);
lean_dec(v___x_2828_);
v___x_2837_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2784_);
v_env_2838_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2837_, v_env_2829_, v_declName_2784_, v_docs_2785_);
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = lean_array_get_size(v_deferred_2786_);
v___x_2841_ = lean_nat_dec_lt(v___x_2839_, v___x_2840_);
if (v___x_2841_ == 0)
{
lean_dec(v_declName_2784_);
v___y_2795_ = v_auxDeclNGen_2832_;
v___y_2796_ = v_messages_2834_;
v___y_2797_ = v___y_2826_;
v___y_2798_ = v_infoState_2835_;
v___y_2799_ = v___y_2827_;
v___y_2800_ = v_snapshotTasks_2836_;
v___y_2801_ = v_traceState_2833_;
v___y_2802_ = v_ngen_2831_;
v___y_2803_ = v_nextMacroScope_2830_;
v___y_2804_ = v_env_2838_;
goto v___jp_2794_;
}
else
{
size_t v___x_2842_; size_t v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = ((size_t)0ULL);
v___x_2843_ = lean_usize_of_nat(v___x_2840_);
v___x_2844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2784_, v_deferred_2786_, v___x_2842_, v___x_2843_, v_env_2838_);
v___y_2795_ = v_auxDeclNGen_2832_;
v___y_2796_ = v_messages_2834_;
v___y_2797_ = v___y_2826_;
v___y_2798_ = v_infoState_2835_;
v___y_2799_ = v___y_2827_;
v___y_2800_ = v_snapshotTasks_2836_;
v___y_2801_ = v_traceState_2833_;
v___y_2802_ = v_ngen_2831_;
v___y_2803_ = v_nextMacroScope_2830_;
v___y_2804_ = v___x_2844_;
goto v___jp_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2867_, lean_object* v_docs_2868_, lean_object* v_deferred_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2867_, v_docs_2868_, v_deferred_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec_ref(v_deferred_2869_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2878_, lean_object* v_binders_2879_, lean_object* v_docComment_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___x_2908_; lean_object* v_env_2909_; lean_object* v___x_2910_; 
v___x_2908_ = lean_st_ref_get(v_a_2886_);
v_env_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc_ref(v_env_2909_);
lean_dec(v___x_2908_);
v___x_2910_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2909_, v_declName_2878_);
lean_dec_ref(v_env_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
v___y_2889_ = v_a_2881_;
v___y_2890_ = v_a_2882_;
v___y_2891_ = v_a_2883_;
v___y_2892_ = v_a_2884_;
v___y_2893_ = v_a_2885_;
v___y_2894_ = v_a_2886_;
goto v___jp_2888_;
}
else
{
lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_binders_2879_);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; 
v_unused_2926_ = lean_ctor_get(v___x_2910_, 0);
lean_dec(v_unused_2926_);
v___x_2912_ = v___x_2910_;
v_isShared_2913_ = v_isSharedCheck_2925_;
goto v_resetjp_2911_;
}
else
{
lean_dec(v___x_2910_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2925_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2914_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2915_ = 1;
v___x_2916_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2878_, v___x_2915_);
v___x_2917_ = lean_string_append(v___x_2914_, v___x_2916_);
lean_dec_ref(v___x_2916_);
v___x_2918_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2919_ = lean_string_append(v___x_2917_, v___x_2918_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set_tag(v___x_2912_, 3);
lean_ctor_set(v___x_2912_, 0, v___x_2919_);
v___x_2921_ = v___x_2912_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = l_Lean_MessageData_ofFormat(v___x_2921_);
v___x_2923_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_2922_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
return v___x_2923_;
}
}
}
v___jp_2888_:
{
lean_object* v___x_2895_; 
lean_inc(v_declName_2878_);
v___x_2895_ = l_Lean_versoDocString(v_declName_2878_, v_binders_2879_, v_docComment_2880_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v_toVersoDocString_2897_; lean_object* v_deferredChecks_2898_; lean_object* v___x_2899_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v_toVersoDocString_2897_ = lean_ctor_get(v_a_2896_, 0);
lean_inc_ref(v_toVersoDocString_2897_);
v_deferredChecks_2898_ = lean_ctor_get(v_a_2896_, 1);
lean_inc_ref(v_deferredChecks_2898_);
lean_dec(v_a_2896_);
v___x_2899_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2878_, v_toVersoDocString_2897_, v_deferredChecks_2898_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
lean_dec_ref(v_deferredChecks_2898_);
return v___x_2899_;
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_declName_2878_);
v_a_2900_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2895_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2895_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2927_, lean_object* v_binders_2928_, lean_object* v_docComment_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_addVersoDocString(v_declName_2927_, v_binders_2928_, v_docComment_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_docComment_2929_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2938_, lean_object* v_docComment_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___x_2967_; lean_object* v_env_2968_; lean_object* v___x_2969_; 
v___x_2967_ = lean_st_ref_get(v_a_2945_);
v_env_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc_ref(v_env_2968_);
lean_dec(v___x_2967_);
v___x_2969_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2968_, v_declName_2938_);
lean_dec_ref(v_env_2968_);
if (lean_obj_tag(v___x_2969_) == 0)
{
v___y_2948_ = v_a_2940_;
v___y_2949_ = v_a_2941_;
v___y_2950_ = v_a_2942_;
v___y_2951_ = v_a_2943_;
v___y_2952_ = v_a_2944_;
v___y_2953_ = v_a_2945_;
goto v___jp_2947_;
}
else
{
lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2984_; 
lean_dec_ref(v_docComment_2939_);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v___x_2969_, 0);
lean_dec(v_unused_2985_);
v___x_2971_ = v___x_2969_;
v_isShared_2972_ = v_isSharedCheck_2984_;
goto v_resetjp_2970_;
}
else
{
lean_dec(v___x_2969_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2984_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; uint8_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2973_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2974_ = 1;
v___x_2975_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2938_, v___x_2974_);
v___x_2976_ = lean_string_append(v___x_2973_, v___x_2975_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2978_ = lean_string_append(v___x_2976_, v___x_2977_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set_tag(v___x_2971_, 3);
lean_ctor_set(v___x_2971_, 0, v___x_2978_);
v___x_2980_ = v___x_2971_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = l_Lean_MessageData_ofFormat(v___x_2980_);
v___x_2982_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_2981_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
return v___x_2982_;
}
}
}
v___jp_2947_:
{
lean_object* v___x_2954_; 
lean_inc(v_declName_2938_);
v___x_2954_ = l_Lean_versoDocStringFromString(v_declName_2938_, v_docComment_2939_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v_toVersoDocString_2956_; lean_object* v_deferredChecks_2957_; lean_object* v___x_2958_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v_toVersoDocString_2956_ = lean_ctor_get(v_a_2955_, 0);
lean_inc_ref(v_toVersoDocString_2956_);
v_deferredChecks_2957_ = lean_ctor_get(v_a_2955_, 1);
lean_inc_ref(v_deferredChecks_2957_);
lean_dec(v_a_2955_);
v___x_2958_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2938_, v_toVersoDocString_2956_, v_deferredChecks_2957_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec_ref(v_deferredChecks_2957_);
return v___x_2958_;
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_declName_2938_);
v_a_2959_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2954_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2954_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2986_, lean_object* v_docComment_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_addVersoDocStringFromString(v_declName_2986_, v_docComment_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2996_, lean_object* v_msgData_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
uint8_t v___x_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = 2;
v___x_3004_ = 0;
v___x_3005_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2996_, v_msgData_2997_, v___x_3003_, v___x_3004_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3006_, lean_object* v_msgData_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3006_, v_msgData_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v_ref_3006_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_3014_, lean_object* v_str_3015_, lean_object* v_as_3016_, size_t v_sz_3017_, size_t v_i_3018_, lean_object* v_b_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_a_3028_; uint8_t v___x_3032_; 
v___x_3032_ = lean_usize_dec_lt(v_i_3018_, v_sz_3017_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_b_3019_);
return v___x_3033_;
}
else
{
lean_object* v_a_3034_; lean_object* v_fst_3035_; lean_object* v_snd_3036_; lean_object* v_start_3037_; lean_object* v_stop_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3058_; 
v_a_3034_ = lean_array_uget_borrowed(v_as_3016_, v_i_3018_);
v_fst_3035_ = lean_ctor_get(v_a_3034_, 0);
lean_inc(v_fst_3035_);
v_snd_3036_ = lean_ctor_get(v_a_3034_, 1);
v_start_3037_ = lean_ctor_get(v_fst_3035_, 0);
v_stop_3038_ = lean_ctor_get(v_fst_3035_, 1);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_fst_3035_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3040_ = v_fst_3035_;
v_isShared_3041_ = v_isSharedCheck_3058_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_stop_3038_);
lean_inc(v_start_3037_);
lean_dec(v_fst_3035_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3058_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_box(0);
if (lean_obj_tag(v___y_3014_) == 1)
{
lean_object* v_val_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v_val_3043_ = lean_ctor_get(v___y_3014_, 0);
v___x_3044_ = lean_nat_add(v_val_3043_, v_start_3037_);
v___x_3045_ = lean_nat_add(v_val_3043_, v_stop_3038_);
v___x_3046_ = 0;
v___x_3047_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3047_, 0, v___x_3044_);
lean_ctor_set(v___x_3047_, 1, v___x_3045_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*2, v___x_3046_);
v___x_3048_ = lean_string_utf8_extract(v_str_3015_, v_start_3037_, v_stop_3038_);
lean_dec(v_stop_3038_);
lean_dec(v_start_3037_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set_tag(v___x_3040_, 2);
lean_ctor_set(v___x_3040_, 1, v___x_3048_);
lean_ctor_set(v___x_3040_, 0, v___x_3047_);
v___x_3050_ = v___x_3040_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_inc(v_snd_3036_);
v___x_3051_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_snd_3036_);
v___x_3052_ = l_Lean_MessageData_ofFormat(v___x_3051_);
v___x_3053_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_3050_, v___x_3052_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec_ref(v___x_3050_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_dec_ref_known(v___x_3053_, 1);
v_a_3028_ = v___x_3042_;
goto v___jp_3027_;
}
else
{
return v___x_3053_;
}
}
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_del_object(v___x_3040_);
lean_dec(v_stop_3038_);
lean_dec(v_start_3037_);
lean_inc(v_snd_3036_);
v___x_3055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3055_, 0, v_snd_3036_);
v___x_3056_ = l_Lean_MessageData_ofFormat(v___x_3055_);
v___x_3057_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_3056_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_dec_ref_known(v___x_3057_, 1);
v_a_3028_ = v___x_3042_;
goto v___jp_3027_;
}
else
{
return v___x_3057_;
}
}
}
}
v___jp_3027_:
{
size_t v___x_3029_; size_t v___x_3030_; 
v___x_3029_ = ((size_t)1ULL);
v___x_3030_ = lean_usize_add(v_i_3018_, v___x_3029_);
v_i_3018_ = v___x_3030_;
v_b_3019_ = v_a_3028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_3059_, lean_object* v_str_3060_, lean_object* v_as_3061_, lean_object* v_sz_3062_, lean_object* v_i_3063_, lean_object* v_b_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
size_t v_sz_boxed_3072_; size_t v_i_boxed_3073_; lean_object* v_res_3074_; 
v_sz_boxed_3072_ = lean_unbox_usize(v_sz_3062_);
lean_dec(v_sz_3062_);
v_i_boxed_3073_ = lean_unbox_usize(v_i_3063_);
lean_dec(v_i_3063_);
v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3059_, v_str_3060_, v_as_3061_, v_sz_boxed_3072_, v_i_boxed_3073_, v_b_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_as_3061_);
lean_dec_ref(v_str_3060_);
lean_dec(v___y_3059_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_str_3083_; lean_object* v___y_3085_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_str_3083_ = l_Lean_TSyntax_getDocString(v_docstring_3075_);
v___x_3100_ = lean_unsigned_to_nat(1u);
v___x_3101_ = l_Lean_Syntax_getArg(v_docstring_3075_, v___x_3100_);
v___x_3102_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_3101_);
lean_dec(v___x_3101_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v___x_3103_; 
v___x_3103_ = lean_box(0);
v___y_3085_ = v___x_3103_;
goto v___jp_3084_;
}
else
{
lean_object* v_val_3104_; uint8_t v___x_3105_; lean_object* v___x_3106_; 
v_val_3104_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3105_ = 0;
v___x_3106_ = l_Lean_SourceInfo_getPos_x3f(v_val_3104_, v___x_3105_);
lean_dec(v_val_3104_);
v___y_3085_ = v___x_3106_;
goto v___jp_3084_;
}
v___jp_3084_:
{
lean_object* v___x_3086_; lean_object* v_fst_3087_; lean_object* v___x_3088_; size_t v_sz_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
lean_inc_ref(v_str_3083_);
v___x_3086_ = l_Lean_rewriteManualLinksCore(v_str_3083_);
v_fst_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_fst_3087_);
lean_dec_ref(v___x_3086_);
v___x_3088_ = lean_box(0);
v_sz_3089_ = lean_array_size(v_fst_3087_);
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3085_, v_str_3083_, v_fst_3087_, v_sz_3089_, v___x_3090_, v___x_3088_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
lean_dec(v_fst_3087_);
lean_dec_ref(v_str_3083_);
lean_dec(v___y_3085_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; 
v_unused_3099_ = lean_ctor_get(v___x_3091_, 0);
lean_dec(v_unused_3099_);
v___x_3093_ = v___x_3091_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_dec(v___x_3091_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3088_);
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3088_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
return v___x_3091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v_docstring_3107_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_3116_, lean_object* v_msg_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_toCold_3125_; lean_object* v_currRecDepth_3126_; lean_object* v_ref_3127_; uint8_t v_diag_3128_; uint8_t v_suppressElabErrors_3129_; lean_object* v_ref_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_toCold_3125_ = lean_ctor_get(v___y_3122_, 0);
v_currRecDepth_3126_ = lean_ctor_get(v___y_3122_, 1);
v_ref_3127_ = lean_ctor_get(v___y_3122_, 2);
v_diag_3128_ = lean_ctor_get_uint8(v___y_3122_, sizeof(void*)*3);
v_suppressElabErrors_3129_ = lean_ctor_get_uint8(v___y_3122_, sizeof(void*)*3 + 1);
v_ref_3130_ = l_Lean_replaceRef(v_ref_3116_, v_ref_3127_);
lean_inc(v_currRecDepth_3126_);
lean_inc_ref(v_toCold_3125_);
v___x_3131_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3131_, 0, v_toCold_3125_);
lean_ctor_set(v___x_3131_, 1, v_currRecDepth_3126_);
lean_ctor_set(v___x_3131_, 2, v_ref_3130_);
lean_ctor_set_uint8(v___x_3131_, sizeof(void*)*3, v_diag_3128_);
lean_ctor_set_uint8(v___x_3131_, sizeof(void*)*3 + 1, v_suppressElabErrors_3129_);
v___x_3132_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_msg_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___x_3131_, v___y_3123_);
lean_dec_ref_known(v___x_3131_, 3);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_3133_, lean_object* v_msg_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_3133_, v_msg_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v_ref_3133_);
return v_res_3142_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_3145_ = l_Lean_stringToMessageData(v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_unsigned_to_nat(1u);
v___x_3162_ = l_Lean_Syntax_getArg(v_stx_3147_, v___x_3161_);
if (lean_obj_tag(v___x_3162_) == 1)
{
lean_object* v_kind_3163_; 
v_kind_3163_ = lean_ctor_get(v___x_3162_, 1);
lean_inc(v_kind_3163_);
if (lean_obj_tag(v_kind_3163_) == 1)
{
lean_object* v_pre_3164_; 
v_pre_3164_ = lean_ctor_get(v_kind_3163_, 0);
lean_inc(v_pre_3164_);
if (lean_obj_tag(v_pre_3164_) == 1)
{
lean_object* v_pre_3165_; 
v_pre_3165_ = lean_ctor_get(v_pre_3164_, 0);
lean_inc(v_pre_3165_);
if (lean_obj_tag(v_pre_3165_) == 1)
{
lean_object* v_pre_3166_; 
v_pre_3166_ = lean_ctor_get(v_pre_3165_, 0);
lean_inc(v_pre_3166_);
if (lean_obj_tag(v_pre_3166_) == 1)
{
lean_object* v_pre_3167_; 
v_pre_3167_ = lean_ctor_get(v_pre_3166_, 0);
if (lean_obj_tag(v_pre_3167_) == 0)
{
lean_object* v_args_3168_; lean_object* v_str_3169_; lean_object* v_str_3170_; lean_object* v_str_3171_; lean_object* v_str_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_args_3168_ = lean_ctor_get(v___x_3162_, 2);
lean_inc_ref(v_args_3168_);
lean_dec_ref_known(v___x_3162_, 3);
v_str_3169_ = lean_ctor_get(v_kind_3163_, 1);
lean_inc_ref(v_str_3169_);
lean_dec_ref_known(v_kind_3163_, 2);
v_str_3170_ = lean_ctor_get(v_pre_3164_, 1);
lean_inc_ref(v_str_3170_);
lean_dec_ref_known(v_pre_3164_, 2);
v_str_3171_ = lean_ctor_get(v_pre_3165_, 1);
lean_inc_ref(v_str_3171_);
lean_dec_ref_known(v_pre_3165_, 2);
v_str_3172_ = lean_ctor_get(v_pre_3166_, 1);
lean_inc_ref(v_str_3172_);
lean_dec_ref_known(v_pre_3166_, 2);
v___x_3173_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_3174_ = lean_string_dec_eq(v_str_3172_, v___x_3173_);
lean_dec_ref(v_str_3172_);
if (v___x_3174_ == 0)
{
lean_dec_ref(v_str_3171_);
lean_dec_ref(v_str_3170_);
lean_dec_ref(v_str_3169_);
lean_dec_ref(v_args_3168_);
goto v___jp_3155_;
}
else
{
lean_object* v___x_3175_; uint8_t v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_3176_ = lean_string_dec_eq(v_str_3171_, v___x_3175_);
lean_dec_ref(v_str_3171_);
if (v___x_3176_ == 0)
{
lean_dec_ref(v_str_3170_);
lean_dec_ref(v_str_3169_);
lean_dec_ref(v_args_3168_);
goto v___jp_3155_;
}
else
{
lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_3178_ = lean_string_dec_eq(v_str_3170_, v___x_3177_);
lean_dec_ref(v_str_3170_);
if (v___x_3178_ == 0)
{
lean_dec_ref(v_str_3169_);
lean_dec_ref(v_args_3168_);
goto v___jp_3155_;
}
else
{
lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2));
v___x_3180_ = lean_string_dec_eq(v_str_3169_, v___x_3179_);
lean_dec_ref(v_str_3169_);
if (v___x_3180_ == 0)
{
lean_dec_ref(v_args_3168_);
goto v___jp_3155_;
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3181_ = lean_array_get_size(v_args_3168_);
v___x_3182_ = lean_unsigned_to_nat(2u);
v___x_3183_ = lean_nat_dec_eq(v___x_3181_, v___x_3182_);
if (v___x_3183_ == 0)
{
lean_dec_ref(v_args_3168_);
goto v___jp_3155_;
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_unsigned_to_nat(0u);
v___x_3185_ = lean_array_fget(v_args_3168_, v___x_3184_);
lean_dec_ref(v_args_3168_);
if (lean_obj_tag(v___x_3185_) == 2)
{
lean_object* v_val_3186_; lean_object* v___x_3187_; 
lean_dec(v_stx_3147_);
v_val_3186_ = lean_ctor_get(v___x_3185_, 1);
lean_inc_ref(v_val_3186_);
lean_dec_ref_known(v___x_3185_, 2);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_val_3186_);
return v___x_3187_;
}
else
{
lean_dec(v___x_3185_);
goto v___jp_3155_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3166_, 2);
lean_dec_ref_known(v_pre_3165_, 2);
lean_dec_ref_known(v_pre_3164_, 2);
lean_dec_ref_known(v_kind_3163_, 2);
lean_dec_ref_known(v___x_3162_, 3);
goto v___jp_3155_;
}
}
else
{
lean_dec(v_pre_3166_);
lean_dec_ref_known(v_pre_3165_, 2);
lean_dec_ref_known(v_pre_3164_, 2);
lean_dec_ref_known(v_kind_3163_, 2);
lean_dec_ref_known(v___x_3162_, 3);
goto v___jp_3155_;
}
}
else
{
lean_dec_ref_known(v_pre_3164_, 2);
lean_dec(v_pre_3165_);
lean_dec_ref_known(v_kind_3163_, 2);
lean_dec_ref_known(v___x_3162_, 3);
goto v___jp_3155_;
}
}
else
{
lean_dec_ref_known(v_kind_3163_, 2);
lean_dec(v_pre_3164_);
lean_dec_ref_known(v___x_3162_, 3);
goto v___jp_3155_;
}
}
else
{
lean_dec(v_kind_3163_);
lean_dec_ref_known(v___x_3162_, 3);
goto v___jp_3155_;
}
}
else
{
lean_dec(v___x_3162_);
goto v___jp_3155_;
}
v___jp_3155_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3156_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3147_);
v___x_3157_ = l_Lean_MessageData_ofSyntax(v_stx_3147_);
v___x_3158_ = l_Lean_indentD(v___x_3157_);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3156_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_stx_3147_, v___x_3159_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v_stx_3147_);
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_3197_, lean_object* v_docComment_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; uint8_t v___x_3269_; 
v___x_3269_ = l_Lean_Name_isAnonymous(v_declName_3197_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v_env_3271_; lean_object* v___x_3272_; 
v___x_3270_ = lean_st_ref_get(v___y_3204_);
v_env_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc_ref(v_env_3271_);
lean_dec(v___x_3270_);
v___x_3272_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3271_, v_declName_3197_);
lean_dec_ref(v_env_3271_);
if (lean_obj_tag(v___x_3272_) == 0)
{
v___y_3207_ = v___y_3199_;
v___y_3208_ = v___y_3200_;
v___y_3209_ = v___y_3201_;
v___y_3210_ = v___y_3202_;
v___y_3211_ = v___y_3203_;
v___y_3212_ = v___y_3204_;
goto v___jp_3206_;
}
else
{
lean_dec_ref_known(v___x_3272_, 1);
if (v___x_3269_ == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_dec(v_docComment_3198_);
v___x_3273_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3274_ = l_Lean_MessageData_ofConstName(v_declName_3197_, v___x_3269_);
v___x_3275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3275_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_3277_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
return v___x_3278_;
}
else
{
v___y_3207_ = v___y_3199_;
v___y_3208_ = v___y_3200_;
v___y_3209_ = v___y_3201_;
v___y_3210_ = v___y_3202_;
v___y_3211_ = v___y_3203_;
v___y_3212_ = v___y_3204_;
goto v___jp_3206_;
}
}
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_dec(v_docComment_3198_);
lean_dec(v_declName_3197_);
v___x_3279_ = lean_box(0);
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
return v___x_3280_;
}
v___jp_3206_:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_3198_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; 
lean_dec_ref_known(v___x_3213_, 1);
v___x_3214_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_3198_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3260_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3217_ = v___x_3214_;
v_isShared_3218_ = v_isSharedCheck_3260_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3260_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v_env_3220_; lean_object* v_nextMacroScope_3221_; lean_object* v_ngen_3222_; lean_object* v_auxDeclNGen_3223_; lean_object* v_traceState_3224_; lean_object* v_messages_3225_; lean_object* v_infoState_3226_; lean_object* v_snapshotTasks_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3258_; 
v___x_3219_ = lean_st_ref_take(v___y_3212_);
v_env_3220_ = lean_ctor_get(v___x_3219_, 0);
v_nextMacroScope_3221_ = lean_ctor_get(v___x_3219_, 1);
v_ngen_3222_ = lean_ctor_get(v___x_3219_, 2);
v_auxDeclNGen_3223_ = lean_ctor_get(v___x_3219_, 3);
v_traceState_3224_ = lean_ctor_get(v___x_3219_, 4);
v_messages_3225_ = lean_ctor_get(v___x_3219_, 6);
v_infoState_3226_ = lean_ctor_get(v___x_3219_, 7);
v_snapshotTasks_3227_ = lean_ctor_get(v___x_3219_, 8);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v___x_3219_, 5);
lean_dec(v_unused_3259_);
v___x_3229_ = v___x_3219_;
v_isShared_3230_ = v_isSharedCheck_3258_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_snapshotTasks_3227_);
lean_inc(v_infoState_3226_);
lean_inc(v_messages_3225_);
lean_inc(v_traceState_3224_);
lean_inc(v_auxDeclNGen_3223_);
lean_inc(v_ngen_3222_);
lean_inc(v_nextMacroScope_3221_);
lean_inc(v_env_3220_);
lean_dec(v___x_3219_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3258_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3231_ = l_Lean_docStringExt;
v___x_3232_ = l_String_removeLeadingSpaces(v_a_3215_);
v___x_3233_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3231_, v_env_3220_, v_declName_3197_, v___x_3232_);
v___x_3234_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 5, v___x_3234_);
lean_ctor_set(v___x_3229_, 0, v___x_3233_);
v___x_3236_ = v___x_3229_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_nextMacroScope_3221_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_ngen_3222_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_auxDeclNGen_3223_);
lean_ctor_set(v_reuseFailAlloc_3257_, 4, v_traceState_3224_);
lean_ctor_set(v_reuseFailAlloc_3257_, 5, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3257_, 6, v_messages_3225_);
lean_ctor_set(v_reuseFailAlloc_3257_, 7, v_infoState_3226_);
lean_ctor_set(v_reuseFailAlloc_3257_, 8, v_snapshotTasks_3227_);
v___x_3236_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v_mctx_3239_; lean_object* v_zetaDeltaFVarIds_3240_; lean_object* v_postponed_3241_; lean_object* v_diag_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3255_; 
v___x_3237_ = lean_st_ref_put(v___y_3212_, v___x_3236_);
v___x_3238_ = lean_st_ref_take(v___y_3210_);
v_mctx_3239_ = lean_ctor_get(v___x_3238_, 0);
v_zetaDeltaFVarIds_3240_ = lean_ctor_get(v___x_3238_, 2);
v_postponed_3241_ = lean_ctor_get(v___x_3238_, 3);
v_diag_3242_ = lean_ctor_get(v___x_3238_, 4);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3255_ == 0)
{
lean_object* v_unused_3256_; 
v_unused_3256_ = lean_ctor_get(v___x_3238_, 1);
lean_dec(v_unused_3256_);
v___x_3244_ = v___x_3238_;
v_isShared_3245_ = v_isSharedCheck_3255_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_diag_3242_);
lean_inc(v_postponed_3241_);
lean_inc(v_zetaDeltaFVarIds_3240_);
lean_inc(v_mctx_3239_);
lean_dec(v___x_3238_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3255_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3246_ = lean_box(0);
v___x_3247_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 1, v___x_3247_);
v___x_3249_ = v___x_3244_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_mctx_3239_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3254_, 2, v_zetaDeltaFVarIds_3240_);
lean_ctor_set(v_reuseFailAlloc_3254_, 3, v_postponed_3241_);
lean_ctor_set(v_reuseFailAlloc_3254_, 4, v_diag_3242_);
v___x_3249_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3250_ = lean_st_ref_put(v___y_3210_, v___x_3249_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3246_);
v___x_3252_ = v___x_3217_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3246_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec(v_declName_3197_);
v_a_3261_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3214_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3214_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
else
{
lean_dec(v_docComment_3198_);
lean_dec(v_declName_3197_);
return v___x_3213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3281_, lean_object* v_docComment_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3281_, v_docComment_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3291_, lean_object* v_declName_3292_, lean_object* v_binders_3293_, lean_object* v_docComment_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
if (v_isVerso_3291_ == 0)
{
lean_object* v___x_3302_; 
lean_dec(v_binders_3293_);
v___x_3302_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3292_, v_docComment_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
return v___x_3302_;
}
else
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_addVersoDocString(v_declName_3292_, v_binders_3293_, v_docComment_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
lean_dec(v_docComment_3294_);
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3304_, lean_object* v_declName_3305_, lean_object* v_binders_3306_, lean_object* v_docComment_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
uint8_t v_isVerso_boxed_3315_; lean_object* v_res_3316_; 
v_isVerso_boxed_3315_ = lean_unbox(v_isVerso_3304_);
v_res_3316_ = l_Lean_addDocStringOf(v_isVerso_boxed_3315_, v_declName_3305_, v_binders_3306_, v_docComment_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3317_, lean_object* v_msgData_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3317_, v_msgData_3318_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3327_, lean_object* v_msgData_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3327_, v_msgData_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v_ref_3327_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_3337_, lean_object* v_ref_3338_, lean_object* v_msg_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_3338_, v_msg_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_3348_, lean_object* v_ref_3349_, lean_object* v_msg_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(v_00_u03b1_3348_, v_ref_3349_, v_msg_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v_ref_3349_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3359_, lean_object* v_t_3360_){
_start:
{
if (lean_obj_tag(v_t_3360_) == 0)
{
lean_object* v_k_3361_; lean_object* v_v_3362_; lean_object* v_l_3363_; lean_object* v_r_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_4018_; 
v_k_3361_ = lean_ctor_get(v_t_3360_, 1);
v_v_3362_ = lean_ctor_get(v_t_3360_, 2);
v_l_3363_ = lean_ctor_get(v_t_3360_, 3);
v_r_3364_ = lean_ctor_get(v_t_3360_, 4);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_t_3360_);
if (v_isSharedCheck_4018_ == 0)
{
lean_object* v_unused_4019_; 
v_unused_4019_ = lean_ctor_get(v_t_3360_, 0);
lean_dec(v_unused_4019_);
v___x_3366_ = v_t_3360_;
v_isShared_3367_ = v_isSharedCheck_4018_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_r_3364_);
lean_inc(v_l_3363_);
lean_inc(v_v_3362_);
lean_inc(v_k_3361_);
lean_dec(v_t_3360_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_4018_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
uint8_t v___x_3368_; 
v___x_3368_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3359_, v_k_3361_);
switch(v___x_3368_)
{
case 0:
{
lean_object* v_impl_3369_; lean_object* v___x_3370_; 
v_impl_3369_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3359_, v_l_3363_);
v___x_3370_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3369_) == 0)
{
if (lean_obj_tag(v_r_3364_) == 0)
{
lean_object* v_size_3371_; lean_object* v_size_3372_; lean_object* v_k_3373_; lean_object* v_v_3374_; lean_object* v_l_3375_; lean_object* v_r_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v_size_3371_ = lean_ctor_get(v_impl_3369_, 0);
lean_inc(v_size_3371_);
v_size_3372_ = lean_ctor_get(v_r_3364_, 0);
v_k_3373_ = lean_ctor_get(v_r_3364_, 1);
v_v_3374_ = lean_ctor_get(v_r_3364_, 2);
v_l_3375_ = lean_ctor_get(v_r_3364_, 3);
lean_inc(v_l_3375_);
v_r_3376_ = lean_ctor_get(v_r_3364_, 4);
v___x_3377_ = lean_unsigned_to_nat(3u);
v___x_3378_ = lean_nat_mul(v___x_3377_, v_size_3371_);
v___x_3379_ = lean_nat_dec_lt(v___x_3378_, v_size_3372_);
lean_dec(v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_dec(v_l_3375_);
v___x_3380_ = lean_nat_add(v___x_3370_, v_size_3371_);
lean_dec(v_size_3371_);
v___x_3381_ = lean_nat_add(v___x_3380_, v_size_3372_);
lean_dec(v___x_3380_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 3, v_impl_3369_);
lean_ctor_set(v___x_3366_, 0, v___x_3381_);
v___x_3383_ = v___x_3366_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3384_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3384_, 3, v_impl_3369_);
lean_ctor_set(v_reuseFailAlloc_3384_, 4, v_r_3364_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
else
{
lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3448_; 
lean_inc(v_r_3376_);
lean_inc(v_v_3374_);
lean_inc(v_k_3373_);
lean_inc(v_size_3372_);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_r_3364_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; lean_object* v_unused_3450_; lean_object* v_unused_3451_; lean_object* v_unused_3452_; lean_object* v_unused_3453_; 
v_unused_3449_ = lean_ctor_get(v_r_3364_, 4);
lean_dec(v_unused_3449_);
v_unused_3450_ = lean_ctor_get(v_r_3364_, 3);
lean_dec(v_unused_3450_);
v_unused_3451_ = lean_ctor_get(v_r_3364_, 2);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_r_3364_, 1);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v_r_3364_, 0);
lean_dec(v_unused_3453_);
v___x_3386_ = v_r_3364_;
v_isShared_3387_ = v_isSharedCheck_3448_;
goto v_resetjp_3385_;
}
else
{
lean_dec(v_r_3364_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3448_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v_size_3388_; lean_object* v_k_3389_; lean_object* v_v_3390_; lean_object* v_l_3391_; lean_object* v_r_3392_; lean_object* v_size_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v_size_3388_ = lean_ctor_get(v_l_3375_, 0);
v_k_3389_ = lean_ctor_get(v_l_3375_, 1);
v_v_3390_ = lean_ctor_get(v_l_3375_, 2);
v_l_3391_ = lean_ctor_get(v_l_3375_, 3);
v_r_3392_ = lean_ctor_get(v_l_3375_, 4);
v_size_3393_ = lean_ctor_get(v_r_3376_, 0);
v___x_3394_ = lean_unsigned_to_nat(2u);
v___x_3395_ = lean_nat_mul(v___x_3394_, v_size_3393_);
v___x_3396_ = lean_nat_dec_lt(v_size_3388_, v___x_3395_);
lean_dec(v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3424_; 
lean_inc(v_r_3392_);
lean_inc(v_l_3391_);
lean_inc(v_v_3390_);
lean_inc(v_k_3389_);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_l_3375_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; lean_object* v_unused_3426_; lean_object* v_unused_3427_; lean_object* v_unused_3428_; lean_object* v_unused_3429_; 
v_unused_3425_ = lean_ctor_get(v_l_3375_, 4);
lean_dec(v_unused_3425_);
v_unused_3426_ = lean_ctor_get(v_l_3375_, 3);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_l_3375_, 2);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_l_3375_, 1);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v_l_3375_, 0);
lean_dec(v_unused_3429_);
v___x_3398_ = v_l_3375_;
v_isShared_3399_ = v_isSharedCheck_3424_;
goto v_resetjp_3397_;
}
else
{
lean_dec(v_l_3375_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3424_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3414_; 
v___x_3400_ = lean_nat_add(v___x_3370_, v_size_3371_);
lean_dec(v_size_3371_);
v___x_3401_ = lean_nat_add(v___x_3400_, v_size_3372_);
lean_dec(v_size_3372_);
if (lean_obj_tag(v_l_3391_) == 0)
{
lean_object* v_size_3422_; 
v_size_3422_ = lean_ctor_get(v_l_3391_, 0);
lean_inc(v_size_3422_);
v___y_3414_ = v_size_3422_;
goto v___jp_3413_;
}
else
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_unsigned_to_nat(0u);
v___y_3414_ = v___x_3423_;
goto v___jp_3413_;
}
v___jp_3402_:
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3406_ = lean_nat_add(v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 4, v_r_3376_);
lean_ctor_set(v___x_3398_, 3, v_r_3392_);
lean_ctor_set(v___x_3398_, 2, v_v_3374_);
lean_ctor_set(v___x_3398_, 1, v_k_3373_);
lean_ctor_set(v___x_3398_, 0, v___x_3406_);
v___x_3408_ = v___x_3398_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_k_3373_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_v_3374_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_r_3392_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_r_3376_);
v___x_3408_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3410_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 4, v___x_3408_);
lean_ctor_set(v___x_3386_, 3, v___y_3403_);
lean_ctor_set(v___x_3386_, 2, v_v_3390_);
lean_ctor_set(v___x_3386_, 1, v_k_3389_);
lean_ctor_set(v___x_3386_, 0, v___x_3401_);
v___x_3410_ = v___x_3386_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_k_3389_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_v_3390_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v___y_3403_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
v___jp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_nat_add(v___x_3400_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec(v___x_3400_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v_l_3391_);
lean_ctor_set(v___x_3366_, 3, v_impl_3369_);
lean_ctor_set(v___x_3366_, 0, v___x_3415_);
v___x_3417_ = v___x_3366_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3421_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3421_, 3, v_impl_3369_);
lean_ctor_set(v_reuseFailAlloc_3421_, 4, v_l_3391_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_nat_add(v___x_3370_, v_size_3393_);
if (lean_obj_tag(v_r_3392_) == 0)
{
lean_object* v_size_3419_; 
v_size_3419_ = lean_ctor_get(v_r_3392_, 0);
lean_inc(v_size_3419_);
v___y_3403_ = v___x_3417_;
v___y_3404_ = v___x_3418_;
v___y_3405_ = v_size_3419_;
goto v___jp_3402_;
}
else
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_unsigned_to_nat(0u);
v___y_3403_ = v___x_3417_;
v___y_3404_ = v___x_3418_;
v___y_3405_ = v___x_3420_;
goto v___jp_3402_;
}
}
}
}
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
lean_del_object(v___x_3366_);
v___x_3430_ = lean_nat_add(v___x_3370_, v_size_3371_);
lean_dec(v_size_3371_);
v___x_3431_ = lean_nat_add(v___x_3430_, v_size_3372_);
lean_dec(v_size_3372_);
v___x_3432_ = lean_nat_add(v___x_3430_, v_size_3388_);
lean_dec(v___x_3430_);
lean_inc_ref(v_impl_3369_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 4, v_l_3375_);
lean_ctor_set(v___x_3386_, 3, v_impl_3369_);
lean_ctor_set(v___x_3386_, 2, v_v_3362_);
lean_ctor_set(v___x_3386_, 1, v_k_3361_);
lean_ctor_set(v___x_3386_, 0, v___x_3432_);
v___x_3434_ = v___x_3386_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_impl_3369_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_l_3375_);
v___x_3434_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_isSharedCheck_3441_ = !lean_is_exclusive(v_impl_3369_);
if (v_isSharedCheck_3441_ == 0)
{
lean_object* v_unused_3442_; lean_object* v_unused_3443_; lean_object* v_unused_3444_; lean_object* v_unused_3445_; lean_object* v_unused_3446_; 
v_unused_3442_ = lean_ctor_get(v_impl_3369_, 4);
lean_dec(v_unused_3442_);
v_unused_3443_ = lean_ctor_get(v_impl_3369_, 3);
lean_dec(v_unused_3443_);
v_unused_3444_ = lean_ctor_get(v_impl_3369_, 2);
lean_dec(v_unused_3444_);
v_unused_3445_ = lean_ctor_get(v_impl_3369_, 1);
lean_dec(v_unused_3445_);
v_unused_3446_ = lean_ctor_get(v_impl_3369_, 0);
lean_dec(v_unused_3446_);
v___x_3436_ = v_impl_3369_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_dec(v_impl_3369_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_r_3376_);
lean_ctor_set(v___x_3436_, 3, v___x_3434_);
lean_ctor_set(v___x_3436_, 2, v_v_3374_);
lean_ctor_set(v___x_3436_, 1, v_k_3373_);
lean_ctor_set(v___x_3436_, 0, v___x_3431_);
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_k_3373_);
lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_v_3374_);
lean_ctor_set(v_reuseFailAlloc_3440_, 3, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3440_, 4, v_r_3376_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v_size_3454_ = lean_ctor_get(v_impl_3369_, 0);
lean_inc(v_size_3454_);
v___x_3455_ = lean_nat_add(v___x_3370_, v_size_3454_);
lean_dec(v_size_3454_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 3, v_impl_3369_);
lean_ctor_set(v___x_3366_, 0, v___x_3455_);
v___x_3457_ = v___x_3366_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_impl_3369_);
lean_ctor_set(v_reuseFailAlloc_3458_, 4, v_r_3364_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
else
{
if (lean_obj_tag(v_r_3364_) == 0)
{
lean_object* v_l_3459_; 
v_l_3459_ = lean_ctor_get(v_r_3364_, 3);
lean_inc(v_l_3459_);
if (lean_obj_tag(v_l_3459_) == 0)
{
lean_object* v_r_3460_; 
v_r_3460_ = lean_ctor_get(v_r_3364_, 4);
lean_inc(v_r_3460_);
if (lean_obj_tag(v_r_3460_) == 0)
{
lean_object* v_size_3461_; lean_object* v_k_3462_; lean_object* v_v_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3476_; 
v_size_3461_ = lean_ctor_get(v_r_3364_, 0);
v_k_3462_ = lean_ctor_get(v_r_3364_, 1);
v_v_3463_ = lean_ctor_get(v_r_3364_, 2);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_r_3364_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; lean_object* v_unused_3478_; 
v_unused_3477_ = lean_ctor_get(v_r_3364_, 4);
lean_dec(v_unused_3477_);
v_unused_3478_ = lean_ctor_get(v_r_3364_, 3);
lean_dec(v_unused_3478_);
v___x_3465_ = v_r_3364_;
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_v_3463_);
lean_inc(v_k_3462_);
lean_inc(v_size_3461_);
lean_dec(v_r_3364_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v_size_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v_size_3467_ = lean_ctor_get(v_l_3459_, 0);
v___x_3468_ = lean_nat_add(v___x_3370_, v_size_3461_);
lean_dec(v_size_3461_);
v___x_3469_ = lean_nat_add(v___x_3370_, v_size_3467_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 4, v_l_3459_);
lean_ctor_set(v___x_3465_, 3, v_impl_3369_);
lean_ctor_set(v___x_3465_, 2, v_v_3362_);
lean_ctor_set(v___x_3465_, 1, v_k_3361_);
lean_ctor_set(v___x_3465_, 0, v___x_3469_);
v___x_3471_ = v___x_3465_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3475_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3475_, 3, v_impl_3369_);
lean_ctor_set(v_reuseFailAlloc_3475_, 4, v_l_3459_);
v___x_3471_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3473_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v_r_3460_);
lean_ctor_set(v___x_3366_, 3, v___x_3471_);
lean_ctor_set(v___x_3366_, 2, v_v_3463_);
lean_ctor_set(v___x_3366_, 1, v_k_3462_);
lean_ctor_set(v___x_3366_, 0, v___x_3468_);
v___x_3473_ = v___x_3366_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_k_3462_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_v_3463_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3474_, 4, v_r_3460_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_k_3479_; lean_object* v_v_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3503_; 
v_k_3479_ = lean_ctor_get(v_r_3364_, 1);
v_v_3480_ = lean_ctor_get(v_r_3364_, 2);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_r_3364_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; lean_object* v_unused_3505_; lean_object* v_unused_3506_; 
v_unused_3504_ = lean_ctor_get(v_r_3364_, 4);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v_r_3364_, 3);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v_r_3364_, 0);
lean_dec(v_unused_3506_);
v___x_3482_ = v_r_3364_;
v_isShared_3483_ = v_isSharedCheck_3503_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_v_3480_);
lean_inc(v_k_3479_);
lean_dec(v_r_3364_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3503_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_k_3484_; lean_object* v_v_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3499_; 
v_k_3484_ = lean_ctor_get(v_l_3459_, 1);
v_v_3485_ = lean_ctor_get(v_l_3459_, 2);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_l_3459_);
if (v_isSharedCheck_3499_ == 0)
{
lean_object* v_unused_3500_; lean_object* v_unused_3501_; lean_object* v_unused_3502_; 
v_unused_3500_ = lean_ctor_get(v_l_3459_, 4);
lean_dec(v_unused_3500_);
v_unused_3501_ = lean_ctor_get(v_l_3459_, 3);
lean_dec(v_unused_3501_);
v_unused_3502_ = lean_ctor_get(v_l_3459_, 0);
lean_dec(v_unused_3502_);
v___x_3487_ = v_l_3459_;
v_isShared_3488_ = v_isSharedCheck_3499_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_v_3485_);
lean_inc(v_k_3484_);
lean_dec(v_l_3459_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3499_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = lean_unsigned_to_nat(3u);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 4, v_r_3460_);
lean_ctor_set(v___x_3487_, 3, v_r_3460_);
lean_ctor_set(v___x_3487_, 2, v_v_3362_);
lean_ctor_set(v___x_3487_, 1, v_k_3361_);
lean_ctor_set(v___x_3487_, 0, v___x_3370_);
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3498_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3498_, 3, v_r_3460_);
lean_ctor_set(v_reuseFailAlloc_3498_, 4, v_r_3460_);
v___x_3491_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 3, v_r_3460_);
lean_ctor_set(v___x_3482_, 0, v___x_3370_);
v___x_3493_ = v___x_3482_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_k_3479_);
lean_ctor_set(v_reuseFailAlloc_3497_, 2, v_v_3480_);
lean_ctor_set(v_reuseFailAlloc_3497_, 3, v_r_3460_);
lean_ctor_set(v_reuseFailAlloc_3497_, 4, v_r_3460_);
v___x_3493_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3495_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v___x_3493_);
lean_ctor_set(v___x_3366_, 3, v___x_3491_);
lean_ctor_set(v___x_3366_, 2, v_v_3485_);
lean_ctor_set(v___x_3366_, 1, v_k_3484_);
lean_ctor_set(v___x_3366_, 0, v___x_3489_);
v___x_3495_ = v___x_3366_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_k_3484_);
lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_v_3485_);
lean_ctor_set(v_reuseFailAlloc_3496_, 3, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3496_, 4, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3507_; 
v_r_3507_ = lean_ctor_get(v_r_3364_, 4);
lean_inc(v_r_3507_);
if (lean_obj_tag(v_r_3507_) == 0)
{
lean_object* v_k_3508_; lean_object* v_v_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3520_; 
v_k_3508_ = lean_ctor_get(v_r_3364_, 1);
v_v_3509_ = lean_ctor_get(v_r_3364_, 2);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_r_3364_);
if (v_isSharedCheck_3520_ == 0)
{
lean_object* v_unused_3521_; lean_object* v_unused_3522_; lean_object* v_unused_3523_; 
v_unused_3521_ = lean_ctor_get(v_r_3364_, 4);
lean_dec(v_unused_3521_);
v_unused_3522_ = lean_ctor_get(v_r_3364_, 3);
lean_dec(v_unused_3522_);
v_unused_3523_ = lean_ctor_get(v_r_3364_, 0);
lean_dec(v_unused_3523_);
v___x_3511_ = v_r_3364_;
v_isShared_3512_ = v_isSharedCheck_3520_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_v_3509_);
lean_inc(v_k_3508_);
lean_dec(v_r_3364_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3520_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3513_ = lean_unsigned_to_nat(3u);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 4, v_l_3459_);
lean_ctor_set(v___x_3511_, 2, v_v_3362_);
lean_ctor_set(v___x_3511_, 1, v_k_3361_);
lean_ctor_set(v___x_3511_, 0, v___x_3370_);
v___x_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3519_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3519_, 3, v_l_3459_);
lean_ctor_set(v_reuseFailAlloc_3519_, 4, v_l_3459_);
v___x_3515_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v_r_3507_);
lean_ctor_set(v___x_3366_, 3, v___x_3515_);
lean_ctor_set(v___x_3366_, 2, v_v_3509_);
lean_ctor_set(v___x_3366_, 1, v_k_3508_);
lean_ctor_set(v___x_3366_, 0, v___x_3513_);
v___x_3517_ = v___x_3366_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_k_3508_);
lean_ctor_set(v_reuseFailAlloc_3518_, 2, v_v_3509_);
lean_ctor_set(v_reuseFailAlloc_3518_, 3, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3518_, 4, v_r_3507_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_object* v_size_3524_; lean_object* v_k_3525_; lean_object* v_v_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3537_; 
v_size_3524_ = lean_ctor_get(v_r_3364_, 0);
v_k_3525_ = lean_ctor_get(v_r_3364_, 1);
v_v_3526_ = lean_ctor_get(v_r_3364_, 2);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_r_3364_);
if (v_isSharedCheck_3537_ == 0)
{
lean_object* v_unused_3538_; lean_object* v_unused_3539_; 
v_unused_3538_ = lean_ctor_get(v_r_3364_, 4);
lean_dec(v_unused_3538_);
v_unused_3539_ = lean_ctor_get(v_r_3364_, 3);
lean_dec(v_unused_3539_);
v___x_3528_ = v_r_3364_;
v_isShared_3529_ = v_isSharedCheck_3537_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_v_3526_);
lean_inc(v_k_3525_);
lean_inc(v_size_3524_);
lean_dec(v_r_3364_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3537_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 3, v_r_3507_);
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_size_3524_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_k_3525_);
lean_ctor_set(v_reuseFailAlloc_3536_, 2, v_v_3526_);
lean_ctor_set(v_reuseFailAlloc_3536_, 3, v_r_3507_);
lean_ctor_set(v_reuseFailAlloc_3536_, 4, v_r_3507_);
v___x_3531_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_unsigned_to_nat(2u);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v___x_3531_);
lean_ctor_set(v___x_3366_, 3, v_r_3507_);
lean_ctor_set(v___x_3366_, 0, v___x_3532_);
v___x_3534_ = v___x_3366_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3535_, 3, v_r_3507_);
lean_ctor_set(v_reuseFailAlloc_3535_, 4, v___x_3531_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
else
{
lean_object* v___x_3541_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 3, v_r_3364_);
lean_ctor_set(v___x_3366_, 0, v___x_3370_);
v___x_3541_ = v___x_3366_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3542_, 3, v_r_3364_);
lean_ctor_set(v_reuseFailAlloc_3542_, 4, v_r_3364_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3366_);
lean_dec(v_v_3362_);
lean_dec(v_k_3361_);
if (lean_obj_tag(v_l_3363_) == 0)
{
if (lean_obj_tag(v_r_3364_) == 0)
{
lean_object* v_size_3543_; lean_object* v_k_3544_; lean_object* v_v_3545_; lean_object* v_l_3546_; lean_object* v_r_3547_; lean_object* v_size_3548_; lean_object* v_k_3549_; lean_object* v_v_3550_; lean_object* v_l_3551_; lean_object* v_r_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_size_3543_ = lean_ctor_get(v_l_3363_, 0);
v_k_3544_ = lean_ctor_get(v_l_3363_, 1);
v_v_3545_ = lean_ctor_get(v_l_3363_, 2);
v_l_3546_ = lean_ctor_get(v_l_3363_, 3);
v_r_3547_ = lean_ctor_get(v_l_3363_, 4);
lean_inc(v_r_3547_);
v_size_3548_ = lean_ctor_get(v_r_3364_, 0);
v_k_3549_ = lean_ctor_get(v_r_3364_, 1);
v_v_3550_ = lean_ctor_get(v_r_3364_, 2);
v_l_3551_ = lean_ctor_get(v_r_3364_, 3);
lean_inc(v_l_3551_);
v_r_3552_ = lean_ctor_get(v_r_3364_, 4);
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = lean_nat_dec_lt(v_size_3543_, v_size_3548_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3690_; 
lean_inc(v_l_3546_);
lean_inc(v_v_3545_);
lean_inc(v_k_3544_);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_l_3363_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; lean_object* v_unused_3695_; 
v_unused_3691_ = lean_ctor_get(v_l_3363_, 4);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_l_3363_, 3);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_l_3363_, 2);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_l_3363_, 1);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_l_3363_, 0);
lean_dec(v_unused_3695_);
v___x_3556_ = v_l_3363_;
v_isShared_3557_ = v_isSharedCheck_3690_;
goto v_resetjp_3555_;
}
else
{
lean_dec(v_l_3363_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3690_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3558_; lean_object* v_tree_3559_; 
v___x_3558_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3544_, v_v_3545_, v_l_3546_, v_r_3547_);
v_tree_3559_ = lean_ctor_get(v___x_3558_, 2);
lean_inc(v_tree_3559_);
if (lean_obj_tag(v_tree_3559_) == 0)
{
lean_object* v_k_3560_; lean_object* v_v_3561_; lean_object* v_size_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v_k_3560_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_k_3560_);
v_v_3561_ = lean_ctor_get(v___x_3558_, 1);
lean_inc(v_v_3561_);
lean_dec_ref(v___x_3558_);
v_size_3562_ = lean_ctor_get(v_tree_3559_, 0);
v___x_3563_ = lean_unsigned_to_nat(3u);
v___x_3564_ = lean_nat_mul(v___x_3563_, v_size_3562_);
v___x_3565_ = lean_nat_dec_lt(v___x_3564_, v_size_3548_);
lean_dec(v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
lean_dec(v_l_3551_);
v___x_3566_ = lean_nat_add(v___x_3553_, v_size_3562_);
v___x_3567_ = lean_nat_add(v___x_3566_, v_size_3548_);
lean_dec(v___x_3566_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 4, v_r_3364_);
lean_ctor_set(v___x_3556_, 3, v_tree_3559_);
lean_ctor_set(v___x_3556_, 2, v_v_3561_);
lean_ctor_set(v___x_3556_, 1, v_k_3560_);
lean_ctor_set(v___x_3556_, 0, v___x_3567_);
v___x_3569_ = v___x_3556_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_k_3560_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_v_3561_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_tree_3559_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v_r_3364_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
else
{
lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3625_; 
lean_inc(v_r_3552_);
lean_inc(v_v_3550_);
lean_inc(v_k_3549_);
lean_inc(v_size_3548_);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_r_3364_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; lean_object* v_unused_3627_; lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3626_ = lean_ctor_get(v_r_3364_, 4);
lean_dec(v_unused_3626_);
v_unused_3627_ = lean_ctor_get(v_r_3364_, 3);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_r_3364_, 2);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_r_3364_, 1);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_r_3364_, 0);
lean_dec(v_unused_3630_);
v___x_3572_ = v_r_3364_;
v_isShared_3573_ = v_isSharedCheck_3625_;
goto v_resetjp_3571_;
}
else
{
lean_dec(v_r_3364_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3625_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v_size_3574_; lean_object* v_k_3575_; lean_object* v_v_3576_; lean_object* v_l_3577_; lean_object* v_r_3578_; lean_object* v_size_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v_size_3574_ = lean_ctor_get(v_l_3551_, 0);
v_k_3575_ = lean_ctor_get(v_l_3551_, 1);
v_v_3576_ = lean_ctor_get(v_l_3551_, 2);
v_l_3577_ = lean_ctor_get(v_l_3551_, 3);
v_r_3578_ = lean_ctor_get(v_l_3551_, 4);
v_size_3579_ = lean_ctor_get(v_r_3552_, 0);
v___x_3580_ = lean_unsigned_to_nat(2u);
v___x_3581_ = lean_nat_mul(v___x_3580_, v_size_3579_);
v___x_3582_ = lean_nat_dec_lt(v_size_3574_, v___x_3581_);
lean_dec(v___x_3581_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3610_; 
lean_inc(v_r_3578_);
lean_inc(v_l_3577_);
lean_inc(v_v_3576_);
lean_inc(v_k_3575_);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_l_3551_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; lean_object* v_unused_3612_; lean_object* v_unused_3613_; lean_object* v_unused_3614_; lean_object* v_unused_3615_; 
v_unused_3611_ = lean_ctor_get(v_l_3551_, 4);
lean_dec(v_unused_3611_);
v_unused_3612_ = lean_ctor_get(v_l_3551_, 3);
lean_dec(v_unused_3612_);
v_unused_3613_ = lean_ctor_get(v_l_3551_, 2);
lean_dec(v_unused_3613_);
v_unused_3614_ = lean_ctor_get(v_l_3551_, 1);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v_l_3551_, 0);
lean_dec(v_unused_3615_);
v___x_3584_ = v_l_3551_;
v_isShared_3585_ = v_isSharedCheck_3610_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v_l_3551_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3610_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3600_; 
v___x_3586_ = lean_nat_add(v___x_3553_, v_size_3562_);
v___x_3587_ = lean_nat_add(v___x_3586_, v_size_3548_);
lean_dec(v_size_3548_);
if (lean_obj_tag(v_l_3577_) == 0)
{
lean_object* v_size_3608_; 
v_size_3608_ = lean_ctor_get(v_l_3577_, 0);
lean_inc(v_size_3608_);
v___y_3600_ = v_size_3608_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_unsigned_to_nat(0u);
v___y_3600_ = v___x_3609_;
goto v___jp_3599_;
}
v___jp_3588_:
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3592_ = lean_nat_add(v___y_3589_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec(v___y_3589_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 4, v_r_3552_);
lean_ctor_set(v___x_3584_, 3, v_r_3578_);
lean_ctor_set(v___x_3584_, 2, v_v_3550_);
lean_ctor_set(v___x_3584_, 1, v_k_3549_);
lean_ctor_set(v___x_3584_, 0, v___x_3592_);
v___x_3594_ = v___x_3584_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3598_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3598_, 3, v_r_3578_);
lean_ctor_set(v_reuseFailAlloc_3598_, 4, v_r_3552_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3596_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 4, v___x_3594_);
lean_ctor_set(v___x_3572_, 3, v___y_3590_);
lean_ctor_set(v___x_3572_, 2, v_v_3576_);
lean_ctor_set(v___x_3572_, 1, v_k_3575_);
lean_ctor_set(v___x_3572_, 0, v___x_3587_);
v___x_3596_ = v___x_3572_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_k_3575_);
lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_v_3576_);
lean_ctor_set(v_reuseFailAlloc_3597_, 3, v___y_3590_);
lean_ctor_set(v_reuseFailAlloc_3597_, 4, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
v___jp_3599_:
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = lean_nat_add(v___x_3586_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec(v___x_3586_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 4, v_l_3577_);
lean_ctor_set(v___x_3556_, 3, v_tree_3559_);
lean_ctor_set(v___x_3556_, 2, v_v_3561_);
lean_ctor_set(v___x_3556_, 1, v_k_3560_);
lean_ctor_set(v___x_3556_, 0, v___x_3601_);
v___x_3603_ = v___x_3556_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3601_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_k_3560_);
lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_v_3561_);
lean_ctor_set(v_reuseFailAlloc_3607_, 3, v_tree_3559_);
lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_l_3577_);
v___x_3603_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3604_; 
v___x_3604_ = lean_nat_add(v___x_3553_, v_size_3579_);
if (lean_obj_tag(v_r_3578_) == 0)
{
lean_object* v_size_3605_; 
v_size_3605_ = lean_ctor_get(v_r_3578_, 0);
lean_inc(v_size_3605_);
v___y_3589_ = v___x_3604_;
v___y_3590_ = v___x_3603_;
v___y_3591_ = v_size_3605_;
goto v___jp_3588_;
}
else
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_unsigned_to_nat(0u);
v___y_3589_ = v___x_3604_;
v___y_3590_ = v___x_3603_;
v___y_3591_ = v___x_3606_;
goto v___jp_3588_;
}
}
}
}
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
v___x_3616_ = lean_nat_add(v___x_3553_, v_size_3562_);
v___x_3617_ = lean_nat_add(v___x_3616_, v_size_3548_);
lean_dec(v_size_3548_);
v___x_3618_ = lean_nat_add(v___x_3616_, v_size_3574_);
lean_dec(v___x_3616_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 4, v_l_3551_);
lean_ctor_set(v___x_3572_, 3, v_tree_3559_);
lean_ctor_set(v___x_3572_, 2, v_v_3561_);
lean_ctor_set(v___x_3572_, 1, v_k_3560_);
lean_ctor_set(v___x_3572_, 0, v___x_3618_);
v___x_3620_ = v___x_3572_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_k_3560_);
lean_ctor_set(v_reuseFailAlloc_3624_, 2, v_v_3561_);
lean_ctor_set(v_reuseFailAlloc_3624_, 3, v_tree_3559_);
lean_ctor_set(v_reuseFailAlloc_3624_, 4, v_l_3551_);
v___x_3620_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3622_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 4, v_r_3552_);
lean_ctor_set(v___x_3556_, 3, v___x_3620_);
lean_ctor_set(v___x_3556_, 2, v_v_3550_);
lean_ctor_set(v___x_3556_, 1, v_k_3549_);
lean_ctor_set(v___x_3556_, 0, v___x_3617_);
v___x_3622_ = v___x_3556_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3623_, 3, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3623_, 4, v_r_3552_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
}
else
{
lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3684_; 
lean_inc(v_r_3552_);
lean_inc(v_v_3550_);
lean_inc(v_k_3549_);
lean_inc(v_size_3548_);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_r_3364_);
if (v_isSharedCheck_3684_ == 0)
{
lean_object* v_unused_3685_; lean_object* v_unused_3686_; lean_object* v_unused_3687_; lean_object* v_unused_3688_; lean_object* v_unused_3689_; 
v_unused_3685_ = lean_ctor_get(v_r_3364_, 4);
lean_dec(v_unused_3685_);
v_unused_3686_ = lean_ctor_get(v_r_3364_, 3);
lean_dec(v_unused_3686_);
v_unused_3687_ = lean_ctor_get(v_r_3364_, 2);
lean_dec(v_unused_3687_);
v_unused_3688_ = lean_ctor_get(v_r_3364_, 1);
lean_dec(v_unused_3688_);
v_unused_3689_ = lean_ctor_get(v_r_3364_, 0);
lean_dec(v_unused_3689_);
v___x_3632_ = v_r_3364_;
v_isShared_3633_ = v_isSharedCheck_3684_;
goto v_resetjp_3631_;
}
else
{
lean_dec(v_r_3364_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3684_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
if (lean_obj_tag(v_l_3551_) == 0)
{
if (lean_obj_tag(v_r_3552_) == 0)
{
lean_object* v_k_3634_; lean_object* v_v_3635_; lean_object* v_size_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3640_; 
v_k_3634_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_k_3634_);
v_v_3635_ = lean_ctor_get(v___x_3558_, 1);
lean_inc(v_v_3635_);
lean_dec_ref(v___x_3558_);
v_size_3636_ = lean_ctor_get(v_l_3551_, 0);
v___x_3637_ = lean_nat_add(v___x_3553_, v_size_3548_);
lean_dec(v_size_3548_);
v___x_3638_ = lean_nat_add(v___x_3553_, v_size_3636_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 4, v_l_3551_);
lean_ctor_set(v___x_3632_, 3, v_tree_3559_);
lean_ctor_set(v___x_3632_, 2, v_v_3635_);
lean_ctor_set(v___x_3632_, 1, v_k_3634_);
lean_ctor_set(v___x_3632_, 0, v___x_3638_);
v___x_3640_ = v___x_3632_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_k_3634_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_v_3635_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_tree_3559_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_l_3551_);
v___x_3640_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3642_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 4, v_r_3552_);
lean_ctor_set(v___x_3556_, 3, v___x_3640_);
lean_ctor_set(v___x_3556_, 2, v_v_3550_);
lean_ctor_set(v___x_3556_, 1, v_k_3549_);
lean_ctor_set(v___x_3556_, 0, v___x_3637_);
v___x_3642_ = v___x_3556_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_r_3552_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
else
{
lean_object* v_k_3645_; lean_object* v_v_3646_; lean_object* v_k_3647_; lean_object* v_v_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_size_3548_);
v_k_3645_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_k_3645_);
v_v_3646_ = lean_ctor_get(v___x_3558_, 1);
lean_inc(v_v_3646_);
lean_dec_ref(v___x_3558_);
v_k_3647_ = lean_ctor_get(v_l_3551_, 1);
v_v_3648_ = lean_ctor_get(v_l_3551_, 2);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_l_3551_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; lean_object* v_unused_3664_; lean_object* v_unused_3665_; 
v_unused_3663_ = lean_ctor_get(v_l_3551_, 4);
lean_dec(v_unused_3663_);
v_unused_3664_ = lean_ctor_get(v_l_3551_, 3);
lean_dec(v_unused_3664_);
v_unused_3665_ = lean_ctor_get(v_l_3551_, 0);
lean_dec(v_unused_3665_);
v___x_3650_ = v_l_3551_;
v_isShared_3651_ = v_isSharedCheck_3662_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_v_3648_);
lean_inc(v_k_3647_);
lean_dec(v_l_3551_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3662_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3652_ = lean_unsigned_to_nat(3u);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 4, v_r_3552_);
lean_ctor_set(v___x_3650_, 3, v_r_3552_);
lean_ctor_set(v___x_3650_, 2, v_v_3646_);
lean_ctor_set(v___x_3650_, 1, v_k_3645_);
lean_ctor_set(v___x_3650_, 0, v___x_3553_);
v___x_3654_ = v___x_3650_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_k_3645_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v_v_3646_);
lean_ctor_set(v_reuseFailAlloc_3661_, 3, v_r_3552_);
lean_ctor_set(v_reuseFailAlloc_3661_, 4, v_r_3552_);
v___x_3654_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 3, v_r_3552_);
lean_ctor_set(v___x_3632_, 0, v___x_3553_);
v___x_3656_ = v___x_3632_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_r_3552_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_r_3552_);
v___x_3656_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 4, v___x_3656_);
lean_ctor_set(v___x_3556_, 3, v___x_3654_);
lean_ctor_set(v___x_3556_, 2, v_v_3648_);
lean_ctor_set(v___x_3556_, 1, v_k_3647_);
lean_ctor_set(v___x_3556_, 0, v___x_3652_);
v___x_3658_ = v___x_3556_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_k_3647_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_v_3648_);
lean_ctor_set(v_reuseFailAlloc_3659_, 3, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3659_, 4, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3552_) == 0)
{
lean_object* v_k_3666_; lean_object* v_v_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
lean_dec(v_size_3548_);
v_k_3666_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_k_3666_);
v_v_3667_ = lean_ctor_get(v___x_3558_, 1);
lean_inc(v_v_3667_);
lean_dec_ref(v___x_3558_);
v___x_3668_ = lean_unsigned_to_nat(3u);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 4, v_l_3551_);
lean_ctor_set(v___x_3632_, 2, v_v_3667_);
lean_ctor_set(v___x_3632_, 1, v_k_3666_);
lean_ctor_set(v___x_3632_, 0, v___x_3553_);
v___x_3670_ = v___x_3632_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_k_3666_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_v_3667_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_l_3551_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_l_3551_);
v___x_3670_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3672_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 4, v_r_3552_);
lean_ctor_set(v___x_3556_, 3, v___x_3670_);
lean_ctor_set(v___x_3556_, 2, v_v_3550_);
lean_ctor_set(v___x_3556_, 1, v_k_3549_);
lean_ctor_set(v___x_3556_, 0, v___x_3668_);
v___x_3672_ = v___x_3556_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3668_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3673_, 3, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_r_3552_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
else
{
lean_object* v_k_3675_; lean_object* v_v_3676_; lean_object* v___x_3678_; 
v_k_3675_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_k_3675_);
v_v_3676_ = lean_ctor_get(v___x_3558_, 1);
lean_inc(v_v_3676_);
lean_dec_ref(v___x_3558_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 3, v_r_3552_);
v___x_3678_ = v___x_3632_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_size_3548_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3683_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3683_, 3, v_r_3552_);
lean_ctor_set(v_reuseFailAlloc_3683_, 4, v_r_3552_);
v___x_3678_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3679_ = lean_unsigned_to_nat(2u);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 4, v___x_3678_);
lean_ctor_set(v___x_3556_, 3, v_r_3552_);
lean_ctor_set(v___x_3556_, 2, v_v_3676_);
lean_ctor_set(v___x_3556_, 1, v_k_3675_);
lean_ctor_set(v___x_3556_, 0, v___x_3679_);
v___x_3681_ = v___x_3556_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_k_3675_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_v_3676_);
lean_ctor_set(v_reuseFailAlloc_3682_, 3, v_r_3552_);
lean_ctor_set(v_reuseFailAlloc_3682_, 4, v___x_3678_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
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
lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3848_; 
lean_inc(v_r_3552_);
lean_inc(v_v_3550_);
lean_inc(v_k_3549_);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_r_3364_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; lean_object* v_unused_3850_; lean_object* v_unused_3851_; lean_object* v_unused_3852_; lean_object* v_unused_3853_; 
v_unused_3849_ = lean_ctor_get(v_r_3364_, 4);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_r_3364_, 3);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v_r_3364_, 2);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_r_3364_, 1);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_r_3364_, 0);
lean_dec(v_unused_3853_);
v___x_3697_ = v_r_3364_;
v_isShared_3698_ = v_isSharedCheck_3848_;
goto v_resetjp_3696_;
}
else
{
lean_dec(v_r_3364_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3848_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; lean_object* v_tree_3700_; 
v___x_3699_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3549_, v_v_3550_, v_l_3551_, v_r_3552_);
v_tree_3700_ = lean_ctor_get(v___x_3699_, 2);
lean_inc(v_tree_3700_);
if (lean_obj_tag(v_tree_3700_) == 0)
{
lean_object* v_k_3701_; lean_object* v_v_3702_; lean_object* v_size_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v_k_3701_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_k_3701_);
v_v_3702_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_v_3702_);
lean_dec_ref(v___x_3699_);
v_size_3703_ = lean_ctor_get(v_tree_3700_, 0);
v___x_3704_ = lean_unsigned_to_nat(3u);
v___x_3705_ = lean_nat_mul(v___x_3704_, v_size_3703_);
v___x_3706_ = lean_nat_dec_lt(v___x_3705_, v_size_3543_);
lean_dec(v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_dec(v_r_3547_);
v___x_3707_ = lean_nat_add(v___x_3553_, v_size_3543_);
v___x_3708_ = lean_nat_add(v___x_3707_, v_size_3703_);
lean_dec(v___x_3707_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v_tree_3700_);
lean_ctor_set(v___x_3697_, 3, v_l_3363_);
lean_ctor_set(v___x_3697_, 2, v_v_3702_);
lean_ctor_set(v___x_3697_, 1, v_k_3701_);
lean_ctor_set(v___x_3697_, 0, v___x_3708_);
v___x_3710_ = v___x_3697_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_k_3701_);
lean_ctor_set(v_reuseFailAlloc_3711_, 2, v_v_3702_);
lean_ctor_set(v_reuseFailAlloc_3711_, 3, v_l_3363_);
lean_ctor_set(v_reuseFailAlloc_3711_, 4, v_tree_3700_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
else
{
lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3777_; 
lean_inc(v_l_3546_);
lean_inc(v_v_3545_);
lean_inc(v_k_3544_);
lean_inc(v_size_3543_);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_l_3363_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; lean_object* v_unused_3779_; lean_object* v_unused_3780_; lean_object* v_unused_3781_; lean_object* v_unused_3782_; 
v_unused_3778_ = lean_ctor_get(v_l_3363_, 4);
lean_dec(v_unused_3778_);
v_unused_3779_ = lean_ctor_get(v_l_3363_, 3);
lean_dec(v_unused_3779_);
v_unused_3780_ = lean_ctor_get(v_l_3363_, 2);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v_l_3363_, 1);
lean_dec(v_unused_3781_);
v_unused_3782_ = lean_ctor_get(v_l_3363_, 0);
lean_dec(v_unused_3782_);
v___x_3713_ = v_l_3363_;
v_isShared_3714_ = v_isSharedCheck_3777_;
goto v_resetjp_3712_;
}
else
{
lean_dec(v_l_3363_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3777_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v_size_3715_; lean_object* v_size_3716_; lean_object* v_k_3717_; lean_object* v_v_3718_; lean_object* v_l_3719_; lean_object* v_r_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v_size_3715_ = lean_ctor_get(v_l_3546_, 0);
v_size_3716_ = lean_ctor_get(v_r_3547_, 0);
v_k_3717_ = lean_ctor_get(v_r_3547_, 1);
v_v_3718_ = lean_ctor_get(v_r_3547_, 2);
v_l_3719_ = lean_ctor_get(v_r_3547_, 3);
v_r_3720_ = lean_ctor_get(v_r_3547_, 4);
v___x_3721_ = lean_unsigned_to_nat(2u);
v___x_3722_ = lean_nat_mul(v___x_3721_, v_size_3715_);
v___x_3723_ = lean_nat_dec_lt(v_size_3716_, v___x_3722_);
lean_dec(v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3761_; 
lean_inc(v_r_3720_);
lean_inc(v_l_3719_);
lean_inc(v_v_3718_);
lean_inc(v_k_3717_);
lean_del_object(v___x_3713_);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_r_3547_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; 
v_unused_3762_ = lean_ctor_get(v_r_3547_, 4);
lean_dec(v_unused_3762_);
v_unused_3763_ = lean_ctor_get(v_r_3547_, 3);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_r_3547_, 2);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_r_3547_, 1);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_r_3547_, 0);
lean_dec(v_unused_3766_);
v___x_3725_ = v_r_3547_;
v_isShared_3726_ = v_isSharedCheck_3761_;
goto v_resetjp_3724_;
}
else
{
lean_dec(v_r_3547_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3761_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___x_3749_; lean_object* v___y_3751_; 
v___x_3727_ = lean_nat_add(v___x_3553_, v_size_3543_);
lean_dec(v_size_3543_);
v___x_3728_ = lean_nat_add(v___x_3727_, v_size_3703_);
lean_dec(v___x_3727_);
v___x_3749_ = lean_nat_add(v___x_3553_, v_size_3715_);
if (lean_obj_tag(v_l_3719_) == 0)
{
lean_object* v_size_3759_; 
v_size_3759_ = lean_ctor_get(v_l_3719_, 0);
lean_inc(v_size_3759_);
v___y_3751_ = v_size_3759_;
goto v___jp_3750_;
}
else
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_unsigned_to_nat(0u);
v___y_3751_ = v___x_3760_;
goto v___jp_3750_;
}
v___jp_3729_:
{
lean_object* v___x_3733_; lean_object* v___x_3735_; 
v___x_3733_ = lean_nat_add(v___y_3730_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec(v___y_3730_);
lean_inc_ref(v_tree_3700_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 4, v_tree_3700_);
lean_ctor_set(v___x_3725_, 3, v_r_3720_);
lean_ctor_set(v___x_3725_, 2, v_v_3702_);
lean_ctor_set(v___x_3725_, 1, v_k_3701_);
lean_ctor_set(v___x_3725_, 0, v___x_3733_);
v___x_3735_ = v___x_3725_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_k_3701_);
lean_ctor_set(v_reuseFailAlloc_3748_, 2, v_v_3702_);
lean_ctor_set(v_reuseFailAlloc_3748_, 3, v_r_3720_);
lean_ctor_set(v_reuseFailAlloc_3748_, 4, v_tree_3700_);
v___x_3735_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_isSharedCheck_3742_ = !lean_is_exclusive(v_tree_3700_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; 
v_unused_3743_ = lean_ctor_get(v_tree_3700_, 4);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_tree_3700_, 3);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_tree_3700_, 2);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_tree_3700_, 1);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_tree_3700_, 0);
lean_dec(v_unused_3747_);
v___x_3737_ = v_tree_3700_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v_tree_3700_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 4, v___x_3735_);
lean_ctor_set(v___x_3737_, 3, v___y_3731_);
lean_ctor_set(v___x_3737_, 2, v_v_3718_);
lean_ctor_set(v___x_3737_, 1, v_k_3717_);
lean_ctor_set(v___x_3737_, 0, v___x_3728_);
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3728_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_k_3717_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_v_3718_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v___y_3731_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v___x_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
v___jp_3750_:
{
lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3752_ = lean_nat_add(v___x_3749_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec(v___x_3749_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v_l_3719_);
lean_ctor_set(v___x_3697_, 3, v_l_3546_);
lean_ctor_set(v___x_3697_, 2, v_v_3545_);
lean_ctor_set(v___x_3697_, 1, v_k_3544_);
lean_ctor_set(v___x_3697_, 0, v___x_3752_);
v___x_3754_ = v___x_3697_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_k_3544_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_v_3545_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_l_3546_);
lean_ctor_set(v_reuseFailAlloc_3758_, 4, v_l_3719_);
v___x_3754_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_nat_add(v___x_3553_, v_size_3703_);
if (lean_obj_tag(v_r_3720_) == 0)
{
lean_object* v_size_3756_; 
v_size_3756_ = lean_ctor_get(v_r_3720_, 0);
lean_inc(v_size_3756_);
v___y_3730_ = v___x_3755_;
v___y_3731_ = v___x_3754_;
v___y_3732_ = v_size_3756_;
goto v___jp_3729_;
}
else
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_unsigned_to_nat(0u);
v___y_3730_ = v___x_3755_;
v___y_3731_ = v___x_3754_;
v___y_3732_ = v___x_3757_;
goto v___jp_3729_;
}
}
}
}
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3767_ = lean_nat_add(v___x_3553_, v_size_3543_);
lean_dec(v_size_3543_);
v___x_3768_ = lean_nat_add(v___x_3767_, v_size_3703_);
lean_dec(v___x_3767_);
v___x_3769_ = lean_nat_add(v___x_3553_, v_size_3703_);
v___x_3770_ = lean_nat_add(v___x_3769_, v_size_3716_);
lean_dec(v___x_3769_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v_tree_3700_);
lean_ctor_set(v___x_3697_, 3, v_r_3547_);
lean_ctor_set(v___x_3697_, 2, v_v_3702_);
lean_ctor_set(v___x_3697_, 1, v_k_3701_);
lean_ctor_set(v___x_3697_, 0, v___x_3770_);
v___x_3772_ = v___x_3697_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_k_3701_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v_v_3702_);
lean_ctor_set(v_reuseFailAlloc_3776_, 3, v_r_3547_);
lean_ctor_set(v_reuseFailAlloc_3776_, 4, v_tree_3700_);
v___x_3772_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3774_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 4, v___x_3772_);
lean_ctor_set(v___x_3713_, 0, v___x_3768_);
v___x_3774_ = v___x_3713_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_k_3544_);
lean_ctor_set(v_reuseFailAlloc_3775_, 2, v_v_3545_);
lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_l_3546_);
lean_ctor_set(v_reuseFailAlloc_3775_, 4, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3546_) == 0)
{
lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3806_; 
lean_inc_ref(v_l_3546_);
lean_inc(v_v_3545_);
lean_inc(v_k_3544_);
lean_inc(v_size_3543_);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_l_3363_);
if (v_isSharedCheck_3806_ == 0)
{
lean_object* v_unused_3807_; lean_object* v_unused_3808_; lean_object* v_unused_3809_; lean_object* v_unused_3810_; lean_object* v_unused_3811_; 
v_unused_3807_ = lean_ctor_get(v_l_3363_, 4);
lean_dec(v_unused_3807_);
v_unused_3808_ = lean_ctor_get(v_l_3363_, 3);
lean_dec(v_unused_3808_);
v_unused_3809_ = lean_ctor_get(v_l_3363_, 2);
lean_dec(v_unused_3809_);
v_unused_3810_ = lean_ctor_get(v_l_3363_, 1);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_l_3363_, 0);
lean_dec(v_unused_3811_);
v___x_3784_ = v_l_3363_;
v_isShared_3785_ = v_isSharedCheck_3806_;
goto v_resetjp_3783_;
}
else
{
lean_dec(v_l_3363_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3806_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
if (lean_obj_tag(v_r_3547_) == 0)
{
lean_object* v_k_3786_; lean_object* v_v_3787_; lean_object* v_size_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3792_; 
v_k_3786_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_k_3786_);
v_v_3787_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_v_3787_);
lean_dec_ref(v___x_3699_);
v_size_3788_ = lean_ctor_get(v_r_3547_, 0);
v___x_3789_ = lean_nat_add(v___x_3553_, v_size_3543_);
lean_dec(v_size_3543_);
v___x_3790_ = lean_nat_add(v___x_3553_, v_size_3788_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v_tree_3700_);
lean_ctor_set(v___x_3697_, 3, v_r_3547_);
lean_ctor_set(v___x_3697_, 2, v_v_3787_);
lean_ctor_set(v___x_3697_, 1, v_k_3786_);
lean_ctor_set(v___x_3697_, 0, v___x_3790_);
v___x_3792_ = v___x_3697_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_k_3786_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_v_3787_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v_r_3547_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v_tree_3700_);
v___x_3792_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3794_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 4, v___x_3792_);
lean_ctor_set(v___x_3784_, 0, v___x_3789_);
v___x_3794_ = v___x_3784_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_k_3544_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_v_3545_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v_l_3546_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
else
{
lean_object* v_k_3797_; lean_object* v_v_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
lean_dec(v_size_3543_);
v_k_3797_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_k_3797_);
v_v_3798_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_v_3798_);
lean_dec_ref(v___x_3699_);
v___x_3799_ = lean_unsigned_to_nat(3u);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v_r_3547_);
lean_ctor_set(v___x_3697_, 3, v_r_3547_);
lean_ctor_set(v___x_3697_, 2, v_v_3798_);
lean_ctor_set(v___x_3697_, 1, v_k_3797_);
lean_ctor_set(v___x_3697_, 0, v___x_3553_);
v___x_3801_ = v___x_3697_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_k_3797_);
lean_ctor_set(v_reuseFailAlloc_3805_, 2, v_v_3798_);
lean_ctor_set(v_reuseFailAlloc_3805_, 3, v_r_3547_);
lean_ctor_set(v_reuseFailAlloc_3805_, 4, v_r_3547_);
v___x_3801_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3803_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 4, v___x_3801_);
lean_ctor_set(v___x_3784_, 0, v___x_3799_);
v___x_3803_ = v___x_3784_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_k_3544_);
lean_ctor_set(v_reuseFailAlloc_3804_, 2, v_v_3545_);
lean_ctor_set(v_reuseFailAlloc_3804_, 3, v_l_3546_);
lean_ctor_set(v_reuseFailAlloc_3804_, 4, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3547_) == 0)
{
lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3836_; 
lean_inc(v_l_3546_);
lean_inc(v_v_3545_);
lean_inc(v_k_3544_);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_l_3363_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; lean_object* v_unused_3838_; lean_object* v_unused_3839_; lean_object* v_unused_3840_; lean_object* v_unused_3841_; 
v_unused_3837_ = lean_ctor_get(v_l_3363_, 4);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_l_3363_, 3);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v_l_3363_, 2);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_l_3363_, 1);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_l_3363_, 0);
lean_dec(v_unused_3841_);
v___x_3813_ = v_l_3363_;
v_isShared_3814_ = v_isSharedCheck_3836_;
goto v_resetjp_3812_;
}
else
{
lean_dec(v_l_3363_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3836_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v_k_3815_; lean_object* v_v_3816_; lean_object* v_k_3817_; lean_object* v_v_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3832_; 
v_k_3815_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_k_3815_);
v_v_3816_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_v_3816_);
lean_dec_ref(v___x_3699_);
v_k_3817_ = lean_ctor_get(v_r_3547_, 1);
v_v_3818_ = lean_ctor_get(v_r_3547_, 2);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_r_3547_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; lean_object* v_unused_3834_; lean_object* v_unused_3835_; 
v_unused_3833_ = lean_ctor_get(v_r_3547_, 4);
lean_dec(v_unused_3833_);
v_unused_3834_ = lean_ctor_get(v_r_3547_, 3);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_r_3547_, 0);
lean_dec(v_unused_3835_);
v___x_3820_ = v_r_3547_;
v_isShared_3821_ = v_isSharedCheck_3832_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_v_3818_);
lean_inc(v_k_3817_);
lean_dec(v_r_3547_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3832_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3822_; lean_object* v___x_3824_; 
v___x_3822_ = lean_unsigned_to_nat(3u);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v_l_3546_);
lean_ctor_set(v___x_3820_, 3, v_l_3546_);
lean_ctor_set(v___x_3820_, 2, v_v_3545_);
lean_ctor_set(v___x_3820_, 1, v_k_3544_);
lean_ctor_set(v___x_3820_, 0, v___x_3553_);
v___x_3824_ = v___x_3820_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_k_3544_);
lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_v_3545_);
lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_l_3546_);
lean_ctor_set(v_reuseFailAlloc_3831_, 4, v_l_3546_);
v___x_3824_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3826_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v_l_3546_);
lean_ctor_set(v___x_3697_, 3, v_l_3546_);
lean_ctor_set(v___x_3697_, 2, v_v_3816_);
lean_ctor_set(v___x_3697_, 1, v_k_3815_);
lean_ctor_set(v___x_3697_, 0, v___x_3553_);
v___x_3826_ = v___x_3697_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_k_3815_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v_v_3816_);
lean_ctor_set(v_reuseFailAlloc_3830_, 3, v_l_3546_);
lean_ctor_set(v_reuseFailAlloc_3830_, 4, v_l_3546_);
v___x_3826_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3828_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 4, v___x_3826_);
lean_ctor_set(v___x_3813_, 3, v___x_3824_);
lean_ctor_set(v___x_3813_, 2, v_v_3818_);
lean_ctor_set(v___x_3813_, 1, v_k_3817_);
lean_ctor_set(v___x_3813_, 0, v___x_3822_);
v___x_3828_ = v___x_3813_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_k_3817_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_v_3818_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v___x_3826_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
}
else
{
lean_object* v_k_3842_; lean_object* v_v_3843_; lean_object* v___x_3844_; lean_object* v___x_3846_; 
v_k_3842_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_k_3842_);
v_v_3843_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_v_3843_);
lean_dec_ref(v___x_3699_);
v___x_3844_ = lean_unsigned_to_nat(2u);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v_r_3547_);
lean_ctor_set(v___x_3697_, 3, v_l_3363_);
lean_ctor_set(v___x_3697_, 2, v_v_3843_);
lean_ctor_set(v___x_3697_, 1, v_k_3842_);
lean_ctor_set(v___x_3697_, 0, v___x_3844_);
v___x_3846_ = v___x_3697_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_k_3842_);
lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_v_3843_);
lean_ctor_set(v_reuseFailAlloc_3847_, 3, v_l_3363_);
lean_ctor_set(v_reuseFailAlloc_3847_, 4, v_r_3547_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
}
}
else
{
return v_l_3363_;
}
}
else
{
return v_r_3364_;
}
}
default: 
{
lean_object* v_impl_3854_; lean_object* v___x_3855_; 
v_impl_3854_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3359_, v_r_3364_);
v___x_3855_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3854_) == 0)
{
if (lean_obj_tag(v_l_3363_) == 0)
{
lean_object* v_size_3856_; lean_object* v_size_3857_; lean_object* v_k_3858_; lean_object* v_v_3859_; lean_object* v_l_3860_; lean_object* v_r_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v_size_3856_ = lean_ctor_get(v_impl_3854_, 0);
lean_inc(v_size_3856_);
v_size_3857_ = lean_ctor_get(v_l_3363_, 0);
v_k_3858_ = lean_ctor_get(v_l_3363_, 1);
v_v_3859_ = lean_ctor_get(v_l_3363_, 2);
v_l_3860_ = lean_ctor_get(v_l_3363_, 3);
v_r_3861_ = lean_ctor_get(v_l_3363_, 4);
lean_inc(v_r_3861_);
v___x_3862_ = lean_unsigned_to_nat(3u);
v___x_3863_ = lean_nat_mul(v___x_3862_, v_size_3856_);
v___x_3864_ = lean_nat_dec_lt(v___x_3863_, v_size_3857_);
lean_dec(v___x_3863_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
lean_dec(v_r_3861_);
v___x_3865_ = lean_nat_add(v___x_3855_, v_size_3857_);
v___x_3866_ = lean_nat_add(v___x_3865_, v_size_3856_);
lean_dec(v_size_3856_);
lean_dec(v___x_3865_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v_impl_3854_);
lean_ctor_set(v___x_3366_, 0, v___x_3866_);
v___x_3868_ = v___x_3366_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3869_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3869_, 3, v_l_3363_);
lean_ctor_set(v_reuseFailAlloc_3869_, 4, v_impl_3854_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
else
{
lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3935_; 
lean_inc(v_l_3860_);
lean_inc(v_v_3859_);
lean_inc(v_k_3858_);
lean_inc(v_size_3857_);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_l_3363_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; lean_object* v_unused_3937_; lean_object* v_unused_3938_; lean_object* v_unused_3939_; lean_object* v_unused_3940_; 
v_unused_3936_ = lean_ctor_get(v_l_3363_, 4);
lean_dec(v_unused_3936_);
v_unused_3937_ = lean_ctor_get(v_l_3363_, 3);
lean_dec(v_unused_3937_);
v_unused_3938_ = lean_ctor_get(v_l_3363_, 2);
lean_dec(v_unused_3938_);
v_unused_3939_ = lean_ctor_get(v_l_3363_, 1);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_l_3363_, 0);
lean_dec(v_unused_3940_);
v___x_3871_ = v_l_3363_;
v_isShared_3872_ = v_isSharedCheck_3935_;
goto v_resetjp_3870_;
}
else
{
lean_dec(v_l_3363_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3935_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v_size_3873_; lean_object* v_size_3874_; lean_object* v_k_3875_; lean_object* v_v_3876_; lean_object* v_l_3877_; lean_object* v_r_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; 
v_size_3873_ = lean_ctor_get(v_l_3860_, 0);
v_size_3874_ = lean_ctor_get(v_r_3861_, 0);
v_k_3875_ = lean_ctor_get(v_r_3861_, 1);
v_v_3876_ = lean_ctor_get(v_r_3861_, 2);
v_l_3877_ = lean_ctor_get(v_r_3861_, 3);
v_r_3878_ = lean_ctor_get(v_r_3861_, 4);
v___x_3879_ = lean_unsigned_to_nat(2u);
v___x_3880_ = lean_nat_mul(v___x_3879_, v_size_3873_);
v___x_3881_ = lean_nat_dec_lt(v_size_3874_, v___x_3880_);
lean_dec(v___x_3880_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3910_; 
lean_inc(v_r_3878_);
lean_inc(v_l_3877_);
lean_inc(v_v_3876_);
lean_inc(v_k_3875_);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_r_3861_);
if (v_isSharedCheck_3910_ == 0)
{
lean_object* v_unused_3911_; lean_object* v_unused_3912_; lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; 
v_unused_3911_ = lean_ctor_get(v_r_3861_, 4);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_r_3861_, 3);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_r_3861_, 2);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_r_3861_, 1);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_r_3861_, 0);
lean_dec(v_unused_3915_);
v___x_3883_ = v_r_3861_;
v_isShared_3884_ = v_isSharedCheck_3910_;
goto v_resetjp_3882_;
}
else
{
lean_dec(v_r_3861_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3910_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___x_3898_; lean_object* v___y_3900_; 
v___x_3885_ = lean_nat_add(v___x_3855_, v_size_3857_);
lean_dec(v_size_3857_);
v___x_3886_ = lean_nat_add(v___x_3885_, v_size_3856_);
lean_dec(v___x_3885_);
v___x_3898_ = lean_nat_add(v___x_3855_, v_size_3873_);
if (lean_obj_tag(v_l_3877_) == 0)
{
lean_object* v_size_3908_; 
v_size_3908_ = lean_ctor_get(v_l_3877_, 0);
lean_inc(v_size_3908_);
v___y_3900_ = v_size_3908_;
goto v___jp_3899_;
}
else
{
lean_object* v___x_3909_; 
v___x_3909_ = lean_unsigned_to_nat(0u);
v___y_3900_ = v___x_3909_;
goto v___jp_3899_;
}
v___jp_3887_:
{
lean_object* v___x_3891_; lean_object* v___x_3893_; 
v___x_3891_ = lean_nat_add(v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec(v___y_3889_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 4, v_impl_3854_);
lean_ctor_set(v___x_3883_, 3, v_r_3878_);
lean_ctor_set(v___x_3883_, 2, v_v_3362_);
lean_ctor_set(v___x_3883_, 1, v_k_3361_);
lean_ctor_set(v___x_3883_, 0, v___x_3891_);
v___x_3893_ = v___x_3883_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3897_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3897_, 3, v_r_3878_);
lean_ctor_set(v_reuseFailAlloc_3897_, 4, v_impl_3854_);
v___x_3893_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3895_; 
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 4, v___x_3893_);
lean_ctor_set(v___x_3871_, 3, v___y_3888_);
lean_ctor_set(v___x_3871_, 2, v_v_3876_);
lean_ctor_set(v___x_3871_, 1, v_k_3875_);
lean_ctor_set(v___x_3871_, 0, v___x_3886_);
v___x_3895_ = v___x_3871_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_k_3875_);
lean_ctor_set(v_reuseFailAlloc_3896_, 2, v_v_3876_);
lean_ctor_set(v_reuseFailAlloc_3896_, 3, v___y_3888_);
lean_ctor_set(v_reuseFailAlloc_3896_, 4, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
v___jp_3899_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = lean_nat_add(v___x_3898_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec(v___x_3898_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v_l_3877_);
lean_ctor_set(v___x_3366_, 3, v_l_3860_);
lean_ctor_set(v___x_3366_, 2, v_v_3859_);
lean_ctor_set(v___x_3366_, 1, v_k_3858_);
lean_ctor_set(v___x_3366_, 0, v___x_3901_);
v___x_3903_ = v___x_3366_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3901_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_k_3858_);
lean_ctor_set(v_reuseFailAlloc_3907_, 2, v_v_3859_);
lean_ctor_set(v_reuseFailAlloc_3907_, 3, v_l_3860_);
lean_ctor_set(v_reuseFailAlloc_3907_, 4, v_l_3877_);
v___x_3903_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_nat_add(v___x_3855_, v_size_3856_);
lean_dec(v_size_3856_);
if (lean_obj_tag(v_r_3878_) == 0)
{
lean_object* v_size_3905_; 
v_size_3905_ = lean_ctor_get(v_r_3878_, 0);
lean_inc(v_size_3905_);
v___y_3888_ = v___x_3903_;
v___y_3889_ = v___x_3904_;
v___y_3890_ = v_size_3905_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_unsigned_to_nat(0u);
v___y_3888_ = v___x_3903_;
v___y_3889_ = v___x_3904_;
v___y_3890_ = v___x_3906_;
goto v___jp_3887_;
}
}
}
}
}
else
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
lean_del_object(v___x_3366_);
v___x_3916_ = lean_nat_add(v___x_3855_, v_size_3857_);
lean_dec(v_size_3857_);
v___x_3917_ = lean_nat_add(v___x_3916_, v_size_3856_);
lean_dec(v___x_3916_);
v___x_3918_ = lean_nat_add(v___x_3855_, v_size_3856_);
lean_dec(v_size_3856_);
v___x_3919_ = lean_nat_add(v___x_3918_, v_size_3874_);
lean_dec(v___x_3918_);
lean_inc_ref(v_impl_3854_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 4, v_impl_3854_);
lean_ctor_set(v___x_3871_, 3, v_r_3861_);
lean_ctor_set(v___x_3871_, 2, v_v_3362_);
lean_ctor_set(v___x_3871_, 1, v_k_3361_);
lean_ctor_set(v___x_3871_, 0, v___x_3919_);
v___x_3921_ = v___x_3871_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v_r_3861_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v_impl_3854_);
v___x_3921_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
v_isSharedCheck_3928_ = !lean_is_exclusive(v_impl_3854_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; lean_object* v_unused_3933_; 
v_unused_3929_ = lean_ctor_get(v_impl_3854_, 4);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_impl_3854_, 3);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_impl_3854_, 2);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_impl_3854_, 1);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_impl_3854_, 0);
lean_dec(v_unused_3933_);
v___x_3923_ = v_impl_3854_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_dec(v_impl_3854_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v___x_3921_);
lean_ctor_set(v___x_3923_, 3, v_l_3860_);
lean_ctor_set(v___x_3923_, 2, v_v_3859_);
lean_ctor_set(v___x_3923_, 1, v_k_3858_);
lean_ctor_set(v___x_3923_, 0, v___x_3917_);
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_k_3858_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_v_3859_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_l_3860_);
lean_ctor_set(v_reuseFailAlloc_3927_, 4, v___x_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3941_; lean_object* v___x_3942_; lean_object* v___x_3944_; 
v_size_3941_ = lean_ctor_get(v_impl_3854_, 0);
lean_inc(v_size_3941_);
v___x_3942_ = lean_nat_add(v___x_3855_, v_size_3941_);
lean_dec(v_size_3941_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v_impl_3854_);
lean_ctor_set(v___x_3366_, 0, v___x_3942_);
v___x_3944_ = v___x_3366_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3945_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3945_, 3, v_l_3363_);
lean_ctor_set(v_reuseFailAlloc_3945_, 4, v_impl_3854_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
else
{
if (lean_obj_tag(v_l_3363_) == 0)
{
lean_object* v_l_3946_; 
v_l_3946_ = lean_ctor_get(v_l_3363_, 3);
if (lean_obj_tag(v_l_3946_) == 0)
{
lean_object* v_r_3947_; 
lean_inc_ref(v_l_3946_);
v_r_3947_ = lean_ctor_get(v_l_3363_, 4);
lean_inc(v_r_3947_);
if (lean_obj_tag(v_r_3947_) == 0)
{
lean_object* v_size_3948_; lean_object* v_k_3949_; lean_object* v_v_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3963_; 
v_size_3948_ = lean_ctor_get(v_l_3363_, 0);
v_k_3949_ = lean_ctor_get(v_l_3363_, 1);
v_v_3950_ = lean_ctor_get(v_l_3363_, 2);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_l_3363_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; lean_object* v_unused_3965_; 
v_unused_3964_ = lean_ctor_get(v_l_3363_, 4);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v_l_3363_, 3);
lean_dec(v_unused_3965_);
v___x_3952_ = v_l_3363_;
v_isShared_3953_ = v_isSharedCheck_3963_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_v_3950_);
lean_inc(v_k_3949_);
lean_inc(v_size_3948_);
lean_dec(v_l_3363_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3963_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v_size_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3958_; 
v_size_3954_ = lean_ctor_get(v_r_3947_, 0);
v___x_3955_ = lean_nat_add(v___x_3855_, v_size_3948_);
lean_dec(v_size_3948_);
v___x_3956_ = lean_nat_add(v___x_3855_, v_size_3954_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 4, v_impl_3854_);
lean_ctor_set(v___x_3952_, 3, v_r_3947_);
lean_ctor_set(v___x_3952_, 2, v_v_3362_);
lean_ctor_set(v___x_3952_, 1, v_k_3361_);
lean_ctor_set(v___x_3952_, 0, v___x_3956_);
v___x_3958_ = v___x_3952_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3962_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3962_, 3, v_r_3947_);
lean_ctor_set(v_reuseFailAlloc_3962_, 4, v_impl_3854_);
v___x_3958_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3960_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v___x_3958_);
lean_ctor_set(v___x_3366_, 3, v_l_3946_);
lean_ctor_set(v___x_3366_, 2, v_v_3950_);
lean_ctor_set(v___x_3366_, 1, v_k_3949_);
lean_ctor_set(v___x_3366_, 0, v___x_3955_);
v___x_3960_ = v___x_3366_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_k_3949_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_v_3950_);
lean_ctor_set(v_reuseFailAlloc_3961_, 3, v_l_3946_);
lean_ctor_set(v_reuseFailAlloc_3961_, 4, v___x_3958_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_object* v_k_3966_; lean_object* v_v_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3978_; 
v_k_3966_ = lean_ctor_get(v_l_3363_, 1);
v_v_3967_ = lean_ctor_get(v_l_3363_, 2);
v_isSharedCheck_3978_ = !lean_is_exclusive(v_l_3363_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; lean_object* v_unused_3980_; lean_object* v_unused_3981_; 
v_unused_3979_ = lean_ctor_get(v_l_3363_, 4);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v_l_3363_, 3);
lean_dec(v_unused_3980_);
v_unused_3981_ = lean_ctor_get(v_l_3363_, 0);
lean_dec(v_unused_3981_);
v___x_3969_ = v_l_3363_;
v_isShared_3970_ = v_isSharedCheck_3978_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_v_3967_);
lean_inc(v_k_3966_);
lean_dec(v_l_3363_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3978_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3971_ = lean_unsigned_to_nat(3u);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 3, v_r_3947_);
lean_ctor_set(v___x_3969_, 2, v_v_3362_);
lean_ctor_set(v___x_3969_, 1, v_k_3361_);
lean_ctor_set(v___x_3969_, 0, v___x_3855_);
v___x_3973_ = v___x_3969_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v_r_3947_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v_r_3947_);
v___x_3973_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
lean_object* v___x_3975_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v___x_3973_);
lean_ctor_set(v___x_3366_, 3, v_l_3946_);
lean_ctor_set(v___x_3366_, 2, v_v_3967_);
lean_ctor_set(v___x_3366_, 1, v_k_3966_);
lean_ctor_set(v___x_3366_, 0, v___x_3971_);
v___x_3975_ = v___x_3366_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3971_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v_k_3966_);
lean_ctor_set(v_reuseFailAlloc_3976_, 2, v_v_3967_);
lean_ctor_set(v_reuseFailAlloc_3976_, 3, v_l_3946_);
lean_ctor_set(v_reuseFailAlloc_3976_, 4, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
}
else
{
lean_object* v_r_3982_; 
v_r_3982_ = lean_ctor_get(v_l_3363_, 4);
lean_inc(v_r_3982_);
if (lean_obj_tag(v_r_3982_) == 0)
{
lean_object* v_k_3983_; lean_object* v_v_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4007_; 
lean_inc(v_l_3946_);
v_k_3983_ = lean_ctor_get(v_l_3363_, 1);
v_v_3984_ = lean_ctor_get(v_l_3363_, 2);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_l_3363_);
if (v_isSharedCheck_4007_ == 0)
{
lean_object* v_unused_4008_; lean_object* v_unused_4009_; lean_object* v_unused_4010_; 
v_unused_4008_ = lean_ctor_get(v_l_3363_, 4);
lean_dec(v_unused_4008_);
v_unused_4009_ = lean_ctor_get(v_l_3363_, 3);
lean_dec(v_unused_4009_);
v_unused_4010_ = lean_ctor_get(v_l_3363_, 0);
lean_dec(v_unused_4010_);
v___x_3986_ = v_l_3363_;
v_isShared_3987_ = v_isSharedCheck_4007_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_v_3984_);
lean_inc(v_k_3983_);
lean_dec(v_l_3363_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4007_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_k_3988_; lean_object* v_v_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4003_; 
v_k_3988_ = lean_ctor_get(v_r_3982_, 1);
v_v_3989_ = lean_ctor_get(v_r_3982_, 2);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_r_3982_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; lean_object* v_unused_4005_; lean_object* v_unused_4006_; 
v_unused_4004_ = lean_ctor_get(v_r_3982_, 4);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v_r_3982_, 3);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v_r_3982_, 0);
lean_dec(v_unused_4006_);
v___x_3991_ = v_r_3982_;
v_isShared_3992_ = v_isSharedCheck_4003_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_v_3989_);
lean_inc(v_k_3988_);
lean_dec(v_r_3982_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4003_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3993_ = lean_unsigned_to_nat(3u);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 4, v_l_3946_);
lean_ctor_set(v___x_3991_, 3, v_l_3946_);
lean_ctor_set(v___x_3991_, 2, v_v_3984_);
lean_ctor_set(v___x_3991_, 1, v_k_3983_);
lean_ctor_set(v___x_3991_, 0, v___x_3855_);
v___x_3995_ = v___x_3991_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_k_3983_);
lean_ctor_set(v_reuseFailAlloc_4002_, 2, v_v_3984_);
lean_ctor_set(v_reuseFailAlloc_4002_, 3, v_l_3946_);
lean_ctor_set(v_reuseFailAlloc_4002_, 4, v_l_3946_);
v___x_3995_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3997_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 4, v_l_3946_);
lean_ctor_set(v___x_3986_, 2, v_v_3362_);
lean_ctor_set(v___x_3986_, 1, v_k_3361_);
lean_ctor_set(v___x_3986_, 0, v___x_3855_);
v___x_3997_ = v___x_3986_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_4001_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_4001_, 3, v_l_3946_);
lean_ctor_set(v_reuseFailAlloc_4001_, 4, v_l_3946_);
v___x_3997_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3999_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v___x_3997_);
lean_ctor_set(v___x_3366_, 3, v___x_3995_);
lean_ctor_set(v___x_3366_, 2, v_v_3989_);
lean_ctor_set(v___x_3366_, 1, v_k_3988_);
lean_ctor_set(v___x_3366_, 0, v___x_3993_);
v___x_3999_ = v___x_3366_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3993_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_k_3988_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_v_3989_);
lean_ctor_set(v_reuseFailAlloc_4000_, 3, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4000_, 4, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4011_ = lean_unsigned_to_nat(2u);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v_r_3982_);
lean_ctor_set(v___x_3366_, 0, v___x_4011_);
v___x_4013_ = v___x_3366_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_4014_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_4014_, 3, v_l_3363_);
lean_ctor_set(v_reuseFailAlloc_4014_, 4, v_r_3982_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
else
{
lean_object* v___x_4016_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 4, v_l_3363_);
lean_ctor_set(v___x_3366_, 0, v___x_3855_);
v___x_4016_ = v___x_3366_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_k_3361_);
lean_ctor_set(v_reuseFailAlloc_4017_, 2, v_v_3362_);
lean_ctor_set(v_reuseFailAlloc_4017_, 3, v_l_3363_);
lean_ctor_set(v_reuseFailAlloc_4017_, 4, v_l_3363_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
}
}
else
{
return v_t_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_4020_, lean_object* v_t_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4020_, v_t_4021_);
lean_dec(v_k_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_4023_, lean_object* v_x_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_4023_, v_x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_4026_, lean_object* v_x_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_4026_, v_x_4027_);
lean_dec(v_declName_4026_);
return v_res_4028_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_4031_ = l_Lean_stringToMessageData(v___x_4030_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___f_4040_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___x_4084_; lean_object* v_env_4085_; lean_object* v___x_4086_; 
lean_inc(v_declName_4032_);
v___f_4040_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4040_, 0, v_declName_4032_);
v___x_4084_ = lean_st_ref_get(v___y_4038_);
v_env_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc_ref(v_env_4085_);
lean_dec(v___x_4084_);
v___x_4086_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4085_, v_declName_4032_);
lean_dec_ref(v_env_4085_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_dec(v_declName_4032_);
v___y_4042_ = v___y_4036_;
v___y_4043_ = v___y_4038_;
goto v___jp_4041_;
}
else
{
uint8_t v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
lean_dec_ref_known(v___x_4086_, 1);
lean_dec_ref(v___f_4040_);
v___x_4087_ = 0;
v___x_4088_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_4089_ = l_Lean_MessageData_ofConstName(v_declName_4032_, v___x_4087_);
v___x_4090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_4092_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
return v___x_4093_;
}
v___jp_4041_:
{
lean_object* v___x_4044_; lean_object* v_env_4045_; lean_object* v_nextMacroScope_4046_; lean_object* v_ngen_4047_; lean_object* v_auxDeclNGen_4048_; lean_object* v_traceState_4049_; lean_object* v_messages_4050_; lean_object* v_infoState_4051_; lean_object* v_snapshotTasks_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4082_; 
v___x_4044_ = lean_st_ref_take(v___y_4043_);
v_env_4045_ = lean_ctor_get(v___x_4044_, 0);
v_nextMacroScope_4046_ = lean_ctor_get(v___x_4044_, 1);
v_ngen_4047_ = lean_ctor_get(v___x_4044_, 2);
v_auxDeclNGen_4048_ = lean_ctor_get(v___x_4044_, 3);
v_traceState_4049_ = lean_ctor_get(v___x_4044_, 4);
v_messages_4050_ = lean_ctor_get(v___x_4044_, 6);
v_infoState_4051_ = lean_ctor_get(v___x_4044_, 7);
v_snapshotTasks_4052_ = lean_ctor_get(v___x_4044_, 8);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4082_ == 0)
{
lean_object* v_unused_4083_; 
v_unused_4083_ = lean_ctor_get(v___x_4044_, 5);
lean_dec(v_unused_4083_);
v___x_4054_ = v___x_4044_;
v_isShared_4055_ = v_isSharedCheck_4082_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_snapshotTasks_4052_);
lean_inc(v_infoState_4051_);
lean_inc(v_messages_4050_);
lean_inc(v_traceState_4049_);
lean_inc(v_auxDeclNGen_4048_);
lean_inc(v_ngen_4047_);
lean_inc(v_nextMacroScope_4046_);
lean_inc(v_env_4045_);
lean_dec(v___x_4044_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4082_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4062_; 
v___x_4056_ = l_Lean_docStringExt;
v___x_4057_ = lean_box(2);
v___x_4058_ = lean_box(0);
v___x_4059_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_4056_, v_env_4045_, v___f_4040_, v___x_4057_, v___x_4058_);
v___x_4060_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 5, v___x_4060_);
lean_ctor_set(v___x_4054_, 0, v___x_4059_);
v___x_4062_ = v___x_4054_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4059_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v_nextMacroScope_4046_);
lean_ctor_set(v_reuseFailAlloc_4081_, 2, v_ngen_4047_);
lean_ctor_set(v_reuseFailAlloc_4081_, 3, v_auxDeclNGen_4048_);
lean_ctor_set(v_reuseFailAlloc_4081_, 4, v_traceState_4049_);
lean_ctor_set(v_reuseFailAlloc_4081_, 5, v___x_4060_);
lean_ctor_set(v_reuseFailAlloc_4081_, 6, v_messages_4050_);
lean_ctor_set(v_reuseFailAlloc_4081_, 7, v_infoState_4051_);
lean_ctor_set(v_reuseFailAlloc_4081_, 8, v_snapshotTasks_4052_);
v___x_4062_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v_mctx_4065_; lean_object* v_zetaDeltaFVarIds_4066_; lean_object* v_postponed_4067_; lean_object* v_diag_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4079_; 
v___x_4063_ = lean_st_ref_put(v___y_4043_, v___x_4062_);
v___x_4064_ = lean_st_ref_take(v___y_4042_);
v_mctx_4065_ = lean_ctor_get(v___x_4064_, 0);
v_zetaDeltaFVarIds_4066_ = lean_ctor_get(v___x_4064_, 2);
v_postponed_4067_ = lean_ctor_get(v___x_4064_, 3);
v_diag_4068_ = lean_ctor_get(v___x_4064_, 4);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4079_ == 0)
{
lean_object* v_unused_4080_; 
v_unused_4080_ = lean_ctor_get(v___x_4064_, 1);
lean_dec(v_unused_4080_);
v___x_4070_ = v___x_4064_;
v_isShared_4071_ = v_isSharedCheck_4079_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_diag_4068_);
lean_inc(v_postponed_4067_);
lean_inc(v_zetaDeltaFVarIds_4066_);
lean_inc(v_mctx_4065_);
lean_dec(v___x_4064_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4079_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4072_ = lean_box(0);
v___x_4073_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 1, v___x_4073_);
v___x_4075_ = v___x_4070_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_mctx_4065_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4078_, 2, v_zetaDeltaFVarIds_4066_);
lean_ctor_set(v_reuseFailAlloc_4078_, 3, v_postponed_4067_);
lean_ctor_set(v_reuseFailAlloc_4078_, 4, v_diag_4068_);
v___x_4075_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_st_ref_put(v___y_4042_, v___x_4075_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4072_);
return v___x_4077_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
return v_res_4102_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_4105_ = l_Lean_stringToMessageData(v___x_4104_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_4108_ = l_Lean_stringToMessageData(v___x_4107_);
return v___x_4108_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_4111_ = l_Lean_stringToMessageData(v___x_4110_);
return v___x_4111_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_4114_ = l_Lean_stringToMessageData(v___x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v___x_4123_; lean_object* v_env_4124_; lean_object* v_ref_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; 
v___x_4123_ = lean_st_ref_get(v_a_4121_);
v_env_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc_ref(v_env_4124_);
lean_dec(v___x_4123_);
v_ref_4125_ = lean_ctor_get(v_a_4120_, 2);
v___x_4126_ = 1;
lean_inc(v_declName_4115_);
v___x_4127_ = l_Lean_findInternalDocString_x3f(v_env_4124_, v_declName_4115_, v___x_4126_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
if (lean_obj_tag(v_a_4128_) == 1)
{
lean_object* v_val_4129_; 
v_val_4129_ = lean_ctor_get(v_a_4128_, 0);
lean_inc(v_val_4129_);
lean_dec_ref_known(v_a_4128_, 1);
if (lean_obj_tag(v_val_4129_) == 0)
{
lean_object* v_val_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4151_; 
v_val_4130_ = lean_ctor_get(v_val_4129_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_val_4129_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4132_ = v_val_4129_;
v_isShared_4133_ = v_isSharedCheck_4151_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_val_4130_);
lean_dec(v_val_4129_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4151_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_removeBuiltinDocString(v_declName_4115_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v___x_4135_; 
lean_dec_ref_known(v___x_4134_, 1);
lean_del_object(v___x_4132_);
lean_inc(v_declName_4115_);
v___x_4135_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v___x_4136_; 
lean_dec_ref_known(v___x_4135_, 1);
v___x_4136_ = l_Lean_addVersoDocStringFromString(v_declName_4115_, v_val_4130_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
return v___x_4136_;
}
else
{
lean_dec(v_val_4130_);
lean_dec(v_declName_4115_);
return v___x_4135_;
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4150_; 
lean_dec(v_val_4130_);
lean_dec(v_declName_4115_);
v_a_4137_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4139_ = v___x_4134_;
v_isShared_4140_ = v_isSharedCheck_4150_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4134_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4150_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4141_ = lean_io_error_to_string(v_a_4137_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 3);
lean_ctor_set(v___x_4132_, 0, v___x_4141_);
v___x_4143_ = v___x_4132_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4144_ = l_Lean_MessageData_ofFormat(v___x_4143_);
lean_inc(v_ref_4125_);
v___x_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4145_, 0, v_ref_4125_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v___x_4145_);
v___x_4147_ = v___x_4139_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
}
else
{
lean_object* v___x_4152_; uint8_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec(v_val_4129_);
v___x_4152_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_4153_ = 0;
v___x_4154_ = l_Lean_MessageData_ofConstName(v_declName_4115_, v___x_4153_);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4152_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4155_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_4157_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
return v___x_4158_;
}
}
else
{
lean_object* v___x_4159_; uint8_t v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_dec(v_a_4128_);
v___x_4159_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_4160_ = 0;
v___x_4161_ = l_Lean_MessageData_ofConstName(v_declName_4115_, v___x_4160_);
v___x_4162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4159_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
v___x_4163_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_4164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_4164_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
return v___x_4165_;
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4177_; 
lean_dec(v_declName_4115_);
v_a_4166_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4168_ = v___x_4127_;
v_isShared_4169_ = v_isSharedCheck_4177_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4127_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4177_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4170_ = lean_io_error_to_string(v_a_4166_);
v___x_4171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
v___x_4172_ = l_Lean_MessageData_ofFormat(v___x_4171_);
lean_inc(v_ref_4125_);
v___x_4173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4173_, 0, v_ref_4125_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4173_);
v___x_4175_ = v___x_4168_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_makeDocStringVerso(v_declName_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_4187_, lean_object* v_k_4188_, lean_object* v_t_4189_, lean_object* v_h_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4188_, v_t_4189_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4192_, lean_object* v_k_4193_, lean_object* v_t_4194_, lean_object* v_h_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_4192_, v_k_4193_, v_t_4194_, v_h_4195_);
lean_dec(v_k_4193_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_4197_, lean_object* v_binders_4198_, lean_object* v_docComment_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
uint8_t v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = l_Lean_isVersoDocComment(v_docComment_4199_);
v___x_4208_ = l_Lean_addDocStringOf(v___x_4207_, v_declName_4197_, v_binders_4198_, v_docComment_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_4209_, lean_object* v_binders_4210_, lean_object* v_docComment_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_addDocString(v_declName_4209_, v_binders_4210_, v_docComment_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_4220_, lean_object* v_binders_4221_, lean_object* v_docString_x3f_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_){
_start:
{
if (lean_obj_tag(v_docString_x3f_4222_) == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_dec(v_binders_4221_);
lean_dec(v_declName_4220_);
v___x_4230_ = lean_box(0);
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
return v___x_4231_;
}
else
{
lean_object* v_val_4232_; lean_object* v___x_4233_; 
v_val_4232_ = lean_ctor_get(v_docString_x3f_4222_, 0);
lean_inc(v_val_4232_);
lean_dec_ref_known(v_docString_x3f_4222_, 1);
v___x_4233_ = l_Lean_addDocString(v_declName_4220_, v_binders_4221_, v_val_4232_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_);
return v___x_4233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_4234_, lean_object* v_binders_4235_, lean_object* v_docString_x3f_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_addDocString_x27(v_declName_4234_, v_binders_4235_, v_docString_x3f_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v___x_4249_; lean_object* v_nextMacroScope_4250_; lean_object* v_ngen_4251_; lean_object* v_auxDeclNGen_4252_; lean_object* v_traceState_4253_; lean_object* v_messages_4254_; lean_object* v_infoState_4255_; lean_object* v_snapshotTasks_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4282_; 
v___x_4249_ = lean_st_ref_take(v___y_4247_);
v_nextMacroScope_4250_ = lean_ctor_get(v___x_4249_, 1);
v_ngen_4251_ = lean_ctor_get(v___x_4249_, 2);
v_auxDeclNGen_4252_ = lean_ctor_get(v___x_4249_, 3);
v_traceState_4253_ = lean_ctor_get(v___x_4249_, 4);
v_messages_4254_ = lean_ctor_get(v___x_4249_, 6);
v_infoState_4255_ = lean_ctor_get(v___x_4249_, 7);
v_snapshotTasks_4256_ = lean_ctor_get(v___x_4249_, 8);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4282_ == 0)
{
lean_object* v_unused_4283_; lean_object* v_unused_4284_; 
v_unused_4283_ = lean_ctor_get(v___x_4249_, 5);
lean_dec(v_unused_4283_);
v_unused_4284_ = lean_ctor_get(v___x_4249_, 0);
lean_dec(v_unused_4284_);
v___x_4258_ = v___x_4249_;
v_isShared_4259_ = v_isSharedCheck_4282_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_snapshotTasks_4256_);
lean_inc(v_infoState_4255_);
lean_inc(v_messages_4254_);
lean_inc(v_traceState_4253_);
lean_inc(v_auxDeclNGen_4252_);
lean_inc(v_ngen_4251_);
lean_inc(v_nextMacroScope_4250_);
lean_dec(v___x_4249_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4282_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4260_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4259_ == 0)
{
lean_ctor_set(v___x_4258_, 5, v___x_4260_);
lean_ctor_set(v___x_4258_, 0, v_env_4245_);
v___x_4262_ = v___x_4258_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_env_4245_);
lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_nextMacroScope_4250_);
lean_ctor_set(v_reuseFailAlloc_4281_, 2, v_ngen_4251_);
lean_ctor_set(v_reuseFailAlloc_4281_, 3, v_auxDeclNGen_4252_);
lean_ctor_set(v_reuseFailAlloc_4281_, 4, v_traceState_4253_);
lean_ctor_set(v_reuseFailAlloc_4281_, 5, v___x_4260_);
lean_ctor_set(v_reuseFailAlloc_4281_, 6, v_messages_4254_);
lean_ctor_set(v_reuseFailAlloc_4281_, 7, v_infoState_4255_);
lean_ctor_set(v_reuseFailAlloc_4281_, 8, v_snapshotTasks_4256_);
v___x_4262_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v_mctx_4265_; lean_object* v_zetaDeltaFVarIds_4266_; lean_object* v_postponed_4267_; lean_object* v_diag_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4279_; 
v___x_4263_ = lean_st_ref_put(v___y_4247_, v___x_4262_);
v___x_4264_ = lean_st_ref_take(v___y_4246_);
v_mctx_4265_ = lean_ctor_get(v___x_4264_, 0);
v_zetaDeltaFVarIds_4266_ = lean_ctor_get(v___x_4264_, 2);
v_postponed_4267_ = lean_ctor_get(v___x_4264_, 3);
v_diag_4268_ = lean_ctor_get(v___x_4264_, 4);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4279_ == 0)
{
lean_object* v_unused_4280_; 
v_unused_4280_ = lean_ctor_get(v___x_4264_, 1);
lean_dec(v_unused_4280_);
v___x_4270_ = v___x_4264_;
v_isShared_4271_ = v_isSharedCheck_4279_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_diag_4268_);
lean_inc(v_postponed_4267_);
lean_inc(v_zetaDeltaFVarIds_4266_);
lean_inc(v_mctx_4265_);
lean_dec(v___x_4264_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4279_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4275_; 
v___x_4272_ = lean_box(0);
v___x_4273_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 1, v___x_4273_);
v___x_4275_ = v___x_4270_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_mctx_4265_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v___x_4273_);
lean_ctor_set(v_reuseFailAlloc_4278_, 2, v_zetaDeltaFVarIds_4266_);
lean_ctor_set(v_reuseFailAlloc_4278_, 3, v_postponed_4267_);
lean_ctor_set(v_reuseFailAlloc_4278_, 4, v_diag_4268_);
v___x_4275_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = lean_st_ref_put(v___y_4246_, v___x_4275_);
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4272_);
return v___x_4277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4285_, v___y_4286_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec(v___y_4286_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_4290_, lean_object* v_as_4291_, size_t v_i_4292_, size_t v_stop_4293_, lean_object* v_b_4294_){
_start:
{
uint8_t v___x_4295_; 
v___x_4295_ = lean_usize_dec_eq(v_i_4292_, v_stop_4293_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v_index_4297_; lean_object* v_sourceString_4298_; lean_object* v_imports_4299_; lean_object* v_currNamespace_4300_; lean_object* v_openDecls_4301_; lean_object* v_options_4302_; lean_object* v_check_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4319_; 
v___x_4296_ = lean_array_uget(v_as_4291_, v_i_4292_);
v_index_4297_ = lean_ctor_get(v___x_4296_, 1);
v_sourceString_4298_ = lean_ctor_get(v___x_4296_, 2);
v_imports_4299_ = lean_ctor_get(v___x_4296_, 3);
v_currNamespace_4300_ = lean_ctor_get(v___x_4296_, 4);
v_openDecls_4301_ = lean_ctor_get(v___x_4296_, 5);
v_options_4302_ = lean_ctor_get(v___x_4296_, 6);
v_check_4303_ = lean_ctor_get(v___x_4296_, 7);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4319_ == 0)
{
lean_object* v_unused_4320_; 
v_unused_4320_ = lean_ctor_get(v___x_4296_, 0);
lean_dec(v_unused_4320_);
v___x_4305_ = v___x_4296_;
v_isShared_4306_ = v_isSharedCheck_4319_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_check_4303_);
lean_inc(v_options_4302_);
lean_inc(v_openDecls_4301_);
lean_inc(v_currNamespace_4300_);
lean_inc(v_imports_4299_);
lean_inc(v_sourceString_4298_);
lean_inc(v_index_4297_);
lean_dec(v___x_4296_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4319_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4307_; lean_object* v_toEnvExtension_4308_; lean_object* v_asyncMode_4309_; lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4307_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_4308_ = lean_ctor_get(v___x_4307_, 0);
v_asyncMode_4309_ = lean_ctor_get(v_toEnvExtension_4308_, 2);
lean_inc(v_n_4290_);
v___x_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4310_, 0, v_n_4290_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4310_);
v___x_4312_ = v___x_4305_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4310_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v_index_4297_);
lean_ctor_set(v_reuseFailAlloc_4318_, 2, v_sourceString_4298_);
lean_ctor_set(v_reuseFailAlloc_4318_, 3, v_imports_4299_);
lean_ctor_set(v_reuseFailAlloc_4318_, 4, v_currNamespace_4300_);
lean_ctor_set(v_reuseFailAlloc_4318_, 5, v_openDecls_4301_);
lean_ctor_set(v_reuseFailAlloc_4318_, 6, v_options_4302_);
lean_ctor_set(v_reuseFailAlloc_4318_, 7, v_check_4303_);
v___x_4312_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; size_t v___x_4315_; size_t v___x_4316_; 
v___x_4313_ = lean_box(0);
v___x_4314_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4307_, v_b_4294_, v___x_4312_, v_asyncMode_4309_, v___x_4313_);
v___x_4315_ = ((size_t)1ULL);
v___x_4316_ = lean_usize_add(v_i_4292_, v___x_4315_);
v_i_4292_ = v___x_4316_;
v_b_4294_ = v___x_4314_;
goto _start;
}
}
}
else
{
lean_dec(v_n_4290_);
return v_b_4294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_4321_, lean_object* v_as_4322_, lean_object* v_i_4323_, lean_object* v_stop_4324_, lean_object* v_b_4325_){
_start:
{
size_t v_i_boxed_4326_; size_t v_stop_boxed_4327_; lean_object* v_res_4328_; 
v_i_boxed_4326_ = lean_unbox_usize(v_i_4323_);
lean_dec(v_i_4323_);
v_stop_boxed_4327_ = lean_unbox_usize(v_stop_4324_);
lean_dec(v_stop_4324_);
v_res_4328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_4321_, v_as_4322_, v_i_boxed_4326_, v_stop_boxed_4327_, v_b_4325_);
lean_dec_ref(v_as_4322_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4329_, lean_object* v_deferred_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v___x_4338_; lean_object* v_env_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4338_ = lean_st_ref_get(v___y_4336_);
v_env_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc_ref(v_env_4339_);
lean_dec(v___x_4338_);
v___x_4340_ = l_Lean_getMainModuleDoc(v_env_4339_);
v___x_4341_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4340_);
lean_dec_ref(v___x_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
lean_dec_ref(v_docs_4329_);
v___x_4342_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_4343_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_4342_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
return v___x_4343_;
}
else
{
lean_object* v___x_4344_; lean_object* v_env_4345_; lean_object* v___x_4346_; lean_object* v_size_4347_; lean_object* v___x_4348_; lean_object* v_env_4349_; lean_object* v___x_4350_; 
v___x_4344_ = lean_st_ref_get(v___y_4336_);
v_env_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc_ref(v_env_4345_);
lean_dec(v___x_4344_);
v___x_4346_ = l_Lean_getMainVersoModuleDocs(v_env_4345_);
v_size_4347_ = lean_ctor_get(v___x_4346_, 2);
lean_inc(v_size_4347_);
lean_dec_ref(v___x_4346_);
v___x_4348_ = lean_st_ref_get(v___y_4336_);
v_env_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc_ref(v_env_4349_);
lean_dec(v___x_4348_);
v___x_4350_ = l_Lean_addVersoModuleDocSnippet(v_env_4349_, v_docs_4329_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
lean_dec(v_size_4347_);
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4352_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4353_ = l_Lean_stringToMessageData(v_a_4351_);
v___x_4354_ = l_Lean_indentD(v___x_4353_);
v___x_4355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4352_);
lean_ctor_set(v___x_4355_, 1, v___x_4354_);
v___x_4356_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v___x_4355_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
return v___x_4356_;
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; uint8_t v___x_4360_; 
v_a_4357_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4358_ = lean_unsigned_to_nat(0u);
v___x_4359_ = lean_array_get_size(v_deferred_4330_);
v___x_4360_ = lean_nat_dec_lt(v___x_4358_, v___x_4359_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; 
lean_dec(v_size_4347_);
v___x_4361_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4357_, v___y_4334_, v___y_4336_);
return v___x_4361_;
}
else
{
size_t v___x_4362_; size_t v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4362_ = ((size_t)0ULL);
v___x_4363_ = lean_usize_of_nat(v___x_4359_);
v___x_4364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4347_, v_deferred_4330_, v___x_4362_, v___x_4363_, v_a_4357_);
v___x_4365_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4364_, v___y_4334_, v___y_4336_);
return v___x_4365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4366_, lean_object* v_deferred_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4366_, v_deferred_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v_deferred_4367_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4376_, lean_object* v_doc_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l_Lean_versoModDocString(v_range_4376_, v_doc_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v_fst_4387_; lean_object* v_snd_4388_; lean_object* v___x_4389_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
v_fst_4387_ = lean_ctor_get(v_a_4386_, 0);
lean_inc(v_fst_4387_);
v_snd_4388_ = lean_ctor_get(v_a_4386_, 1);
lean_inc(v_snd_4388_);
lean_dec(v_a_4386_);
v___x_4389_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_4387_, v_snd_4388_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_);
lean_dec(v_snd_4388_);
return v___x_4389_;
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
v_a_4390_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4385_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4385_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4398_, lean_object* v_doc_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_addVersoModDocString(v_range_4398_, v_doc_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
lean_dec(v_doc_4399_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4408_, v___y_4412_, v___y_4414_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
return v_res_4425_;
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

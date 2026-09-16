// Lean compiler output
// Module: Lean.Elab.Tactic.Doc
// Imports: import Lean.DocString import Lean.DocString.Add import Lean.Elab.DocString public import Lean.Elab.Command public import Lean.Parser.Tactic.Doc
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_isVersoDocComment(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_BlockCtxt_forDocString(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_documentFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Add_0__Lean_parseErrors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange(lean_object*);
lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
lean_object* l_Lean_Doc_elabBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Doc_joinInlines(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_withRendererFallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object*);
lean_object* l_Lean_Doc_joinBlocks(lean_object*);
lean_object* l_Lean_Doc_prefixListLines(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Doc_prefixLines(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_MarkdownM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_withExprHover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_constants(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
extern lean_object* l_Lean_Parser_parserExtension;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_nestD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__0_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__1_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__3_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__3_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7_value),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__11_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__12 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__12_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__9_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__9_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__10_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__13;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__15 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__15_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__16 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__16_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__17 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed__const__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__12(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__1_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__1_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__0_value)} };
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___lam__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unexpected '"};
static const lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tactic_extension"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 244, 145, 122, 23, 135, 199, 68)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Malformed tactic extension command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Missing documentation comment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabTacticExtension"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 44, 144, 107, 80, 40, 109, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Malformed 'register_tactic_tag' command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_tactic_tag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 57, 11, 65, 76, 175, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabRegisterTacticTag"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 30, 89, 153, 147, 186, 30, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__5_value),LEAN_SCALAR_PTR_LITERAL(158, 68, 185, 128, 48, 210, 24, 186)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_param___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " — \""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value;
static const lean_ctor_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value)}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Available tags: "};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "printTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 105, 20, 120, 144, 238, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabPrintTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 38, 126, 200, 28, 172, 117, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Displays all available tactic tags, with documentation.\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__13(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_28_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__10));
v___x_29_ = lean_unsigned_to_nat(3u);
v___x_30_ = lean_mk_empty_array_with_capacity(v___x_29_);
v___x_31_ = lean_array_push(v___x_30_, v___x_28_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed(lean_object* v_x_36_, lean_object* v_x_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(v_x_36_, v_x_37_, v_a_38_, v_a_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___lam__0___boxed(lean_object* v_x_45_, lean_object* v_sz_46_, lean_object* v___x_47_, lean_object* v_content_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
size_t v_sz_boxed_53_; size_t v___x_11953__boxed_54_; lean_object* v_res_55_; 
v_sz_boxed_53_ = lean_unbox_usize(v_sz_46_);
lean_dec(v_sz_46_);
v___x_11953__boxed_54_ = lean_unbox_usize(v___x_47_);
lean_dec(v___x_47_);
v_res_55_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___lam__0(v_x_45_, v_sz_boxed_53_, v___x_11953__boxed_54_, v_content_48_, v___y_49_, v___y_50_, v___y_51_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_pieces_63_; lean_object* v_pieces_67_; 
switch(lean_obj_tag(v_x_57_))
{
case 0:
{
lean_object* v_string_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec_ref(v_x_56_);
v_string_70_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_string_70_);
lean_dec_ref_known(v_x_57_, 1);
v___x_71_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_70_);
lean_dec_ref(v_string_70_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_mk_empty_array_with_capacity(v___x_72_);
v___x_74_ = lean_array_push(v___x_73_, v___x_71_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
case 1:
{
lean_object* v_content_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_127_; 
v_content_76_ = lean_ctor_get(v_x_57_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_127_ == 0)
{
v___x_78_ = v_x_57_;
v_isShared_79_ = v_isSharedCheck_127_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_content_76_);
lean_dec(v_x_57_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_127_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 9);
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_content_76_);
v___x_81_ = v_reuseFailAlloc_126_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; lean_object* v_snd_83_; lean_object* v_fst_84_; lean_object* v_fst_85_; lean_object* v_snd_86_; lean_object* v_pieces_88_; uint8_t v_inEmph_96_; uint8_t v_inBold_97_; uint8_t v_inLink_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_125_; 
v___x_82_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_81_);
v_snd_83_ = lean_ctor_get(v___x_82_, 1);
lean_inc(v_snd_83_);
v_fst_84_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_fst_84_);
lean_dec_ref(v___x_82_);
v_fst_85_ = lean_ctor_get(v_snd_83_, 0);
lean_inc(v_fst_85_);
v_snd_86_ = lean_ctor_get(v_snd_83_, 1);
lean_inc(v_snd_86_);
lean_dec(v_snd_83_);
v_inEmph_96_ = lean_ctor_get_uint8(v_x_56_, 0);
v_inBold_97_ = lean_ctor_get_uint8(v_x_56_, 1);
v_inLink_98_ = lean_ctor_get_uint8(v_x_56_, 2);
v_isSharedCheck_125_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_125_ == 0)
{
v___x_100_ = v_x_56_;
v_isShared_101_ = v_isSharedCheck_125_;
goto v_resetjp_99_;
}
else
{
lean_dec(v_x_56_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_125_;
goto v_resetjp_99_;
}
v___jp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_89_ = lean_string_utf8_byte_size(v_snd_86_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_nat_dec_eq(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_mk_empty_array_with_capacity(v___x_92_);
v___x_94_ = lean_array_push(v___x_93_, v_snd_86_);
v___x_95_ = lean_array_push(v_pieces_88_, v___x_94_);
v_pieces_67_ = v___x_95_;
goto v___jp_66_;
}
else
{
lean_dec(v_snd_86_);
v_pieces_67_ = v_pieces_88_;
goto v___jp_66_;
}
}
v_resetjp_99_:
{
uint8_t v___x_102_; lean_object* v___x_104_; 
v___x_102_ = 1;
if (v_isShared_101_ == 0)
{
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_124_, 1, v_inBold_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_124_, 2, v_inLink_98_);
v___x_104_ = v_reuseFailAlloc_124_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
lean_ctor_set_uint8(v___x_104_, 0, v___x_102_);
v___x_105_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(v___x_104_, v_fst_85_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_pieces_108_; lean_object* v_pieces_113_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__2));
v___x_118_ = lean_string_utf8_byte_size(v_fst_84_);
v___x_119_ = lean_nat_dec_eq(v___x_118_, v___x_116_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
v___x_122_ = lean_array_push(v___x_121_, v_fst_84_);
v___x_123_ = lean_array_push(v___x_117_, v___x_122_);
v_pieces_113_ = v___x_123_;
goto v___jp_112_;
}
else
{
lean_dec(v_fst_84_);
v_pieces_113_ = v___x_117_;
goto v___jp_112_;
}
v___jp_107_:
{
lean_object* v___x_109_; 
v___x_109_ = lean_array_push(v_pieces_108_, v_a_106_);
if (v_inEmph_96_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__1));
v___x_111_ = lean_array_push(v___x_109_, v___x_110_);
v_pieces_88_ = v___x_111_;
goto v___jp_87_;
}
else
{
v_pieces_88_ = v___x_109_;
goto v___jp_87_;
}
}
v___jp_112_:
{
if (v_inEmph_96_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__1));
v___x_115_ = lean_array_push(v_pieces_113_, v___x_114_);
v_pieces_108_ = v___x_115_;
goto v___jp_107_;
}
else
{
v_pieces_108_ = v_pieces_113_;
goto v___jp_107_;
}
}
}
else
{
lean_dec(v_snd_86_);
lean_dec(v_fst_84_);
return v___x_105_;
}
}
}
}
}
}
case 2:
{
lean_object* v_content_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_179_; 
v_content_128_ = lean_ctor_get(v_x_57_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_179_ == 0)
{
v___x_130_ = v_x_57_;
v_isShared_131_ = v_isSharedCheck_179_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_content_128_);
lean_dec(v_x_57_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_179_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 9);
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_content_128_);
v___x_133_ = v_reuseFailAlloc_178_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v_snd_135_; lean_object* v_fst_136_; lean_object* v_fst_137_; lean_object* v_snd_138_; lean_object* v_pieces_140_; uint8_t v_inEmph_148_; uint8_t v_inBold_149_; uint8_t v_inLink_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_177_; 
v___x_134_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_133_);
v_snd_135_ = lean_ctor_get(v___x_134_, 1);
lean_inc(v_snd_135_);
v_fst_136_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_fst_136_);
lean_dec_ref(v___x_134_);
v_fst_137_ = lean_ctor_get(v_snd_135_, 0);
lean_inc(v_fst_137_);
v_snd_138_ = lean_ctor_get(v_snd_135_, 1);
lean_inc(v_snd_138_);
lean_dec(v_snd_135_);
v_inEmph_148_ = lean_ctor_get_uint8(v_x_56_, 0);
v_inBold_149_ = lean_ctor_get_uint8(v_x_56_, 1);
v_inLink_150_ = lean_ctor_get_uint8(v_x_56_, 2);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_177_ == 0)
{
v___x_152_ = v_x_56_;
v_isShared_153_ = v_isSharedCheck_177_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_x_56_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_177_;
goto v_resetjp_151_;
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = lean_string_utf8_byte_size(v_snd_138_);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_nat_dec_eq(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_mk_empty_array_with_capacity(v___x_144_);
v___x_146_ = lean_array_push(v___x_145_, v_snd_138_);
v___x_147_ = lean_array_push(v_pieces_140_, v___x_146_);
v_pieces_63_ = v___x_147_;
goto v___jp_62_;
}
else
{
lean_dec(v_snd_138_);
v_pieces_63_ = v_pieces_140_;
goto v___jp_62_;
}
}
v_resetjp_151_:
{
uint8_t v___x_154_; lean_object* v___x_156_; 
v___x_154_ = 1;
if (v_isShared_153_ == 0)
{
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, 0, v_inEmph_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, 2, v_inLink_150_);
v___x_156_ = v_reuseFailAlloc_176_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; 
lean_ctor_set_uint8(v___x_156_, 1, v___x_154_);
v___x_157_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(v___x_156_, v_fst_137_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v_pieces_160_; lean_object* v_pieces_165_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__2));
v___x_170_ = lean_string_utf8_byte_size(v_fst_136_);
v___x_171_ = lean_nat_dec_eq(v___x_170_, v___x_168_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_174_ = lean_array_push(v___x_173_, v_fst_136_);
v___x_175_ = lean_array_push(v___x_169_, v___x_174_);
v_pieces_165_ = v___x_175_;
goto v___jp_164_;
}
else
{
lean_dec(v_fst_136_);
v_pieces_165_ = v___x_169_;
goto v___jp_164_;
}
v___jp_159_:
{
lean_object* v___x_161_; 
v___x_161_ = lean_array_push(v_pieces_160_, v_a_158_);
if (v_inBold_149_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__4));
v___x_163_ = lean_array_push(v___x_161_, v___x_162_);
v_pieces_140_ = v___x_163_;
goto v___jp_139_;
}
else
{
v_pieces_140_ = v___x_161_;
goto v___jp_139_;
}
}
v___jp_164_:
{
if (v_inBold_149_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__4));
v___x_167_ = lean_array_push(v_pieces_165_, v___x_166_);
v_pieces_160_ = v___x_167_;
goto v___jp_159_;
}
else
{
v_pieces_160_ = v_pieces_165_;
goto v___jp_159_;
}
}
}
else
{
lean_dec(v_snd_138_);
lean_dec(v_fst_136_);
return v___x_157_;
}
}
}
}
}
}
case 3:
{
lean_object* v_string_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec_ref(v_x_56_);
v_string_180_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_string_180_);
lean_dec_ref_known(v_x_57_, 1);
v___x_181_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_180_);
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_mk_empty_array_with_capacity(v___x_182_);
v___x_184_ = lean_array_push(v___x_183_, v___x_181_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
case 4:
{
uint8_t v_mode_186_; 
lean_dec_ref(v_x_56_);
v_mode_186_ = lean_ctor_get_uint8(v_x_57_, sizeof(void*)*1);
if (v_mode_186_ == 0)
{
lean_object* v_string_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_string_187_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_string_187_);
lean_dec_ref_known(v_x_57_, 1);
v___x_188_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__5));
v___x_189_ = lean_string_append(v___x_188_, v_string_187_);
lean_dec_ref(v_string_187_);
v___x_190_ = lean_string_append(v___x_189_, v___x_188_);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_mk_empty_array_with_capacity(v___x_191_);
v___x_193_ = lean_array_push(v___x_192_, v___x_190_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v_string_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_string_195_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_string_195_);
lean_dec_ref_known(v_x_57_, 1);
v___x_196_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__6));
v___x_197_ = lean_string_append(v___x_196_, v_string_195_);
lean_dec_ref(v_string_195_);
v___x_198_ = lean_string_append(v___x_197_, v___x_196_);
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_mk_empty_array_with_capacity(v___x_199_);
v___x_201_ = lean_array_push(v___x_200_, v___x_198_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
case 5:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec_ref_known(v_x_57_, 1);
lean_dec_ref(v_x_56_);
v___x_203_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__8));
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
case 6:
{
uint8_t v_inLink_205_; 
v_inLink_205_ = lean_ctor_get_uint8(v_x_56_, 2);
if (v_inLink_205_ == 0)
{
lean_object* v_content_206_; lean_object* v_url_207_; uint8_t v_inEmph_208_; uint8_t v_inBold_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_238_; 
v_content_206_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_content_206_);
v_url_207_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_url_207_);
lean_dec_ref_known(v_x_57_, 2);
v_inEmph_208_ = lean_ctor_get_uint8(v_x_56_, 0);
v_inBold_209_ = lean_ctor_get_uint8(v_x_56_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_x_56_);
if (v_isSharedCheck_238_ == 0)
{
v___x_211_ = v_x_56_;
v_isShared_212_ = v_isSharedCheck_238_;
goto v_resetjp_210_;
}
else
{
lean_dec(v_x_56_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_238_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
uint8_t v___x_213_; lean_object* v___x_215_; 
v___x_213_ = 1;
if (v_isShared_212_ == 0)
{
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 0, v_inEmph_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, 1, v_inBold_209_);
v___x_215_ = v_reuseFailAlloc_237_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_ctor_set_uint8(v___x_215_, 2, v___x_213_);
v___x_216_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_216_, 0, v_content_206_);
v___x_217_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(v___x_215_, v___x_216_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_236_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_236_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_236_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_236_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_mk_empty_array_with_capacity(v___x_222_);
v___x_224_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__11));
v___x_225_ = lean_string_append(v___x_224_, v_url_207_);
lean_dec_ref(v_url_207_);
v___x_226_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__12));
v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
v___x_228_ = lean_array_push(v___x_223_, v___x_227_);
v___x_229_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__13, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__13_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__13);
v___x_230_ = lean_array_push(v___x_229_, v_a_218_);
v___x_231_ = lean_array_push(v___x_230_, v___x_228_);
v___x_232_ = l_Lean_Doc_joinInlines(v___x_231_);
lean_dec_ref(v___x_231_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_232_);
v___x_234_ = v___x_220_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_dec_ref(v_url_207_);
return v___x_217_;
}
}
}
}
else
{
lean_object* v_content_239_; size_t v_sz_240_; size_t v___x_241_; lean_object* v___x_242_; 
v_content_239_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_content_239_);
lean_dec_ref_known(v_x_57_, 2);
v_sz_240_ = lean_array_size(v_content_239_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(v_x_56_, v_sz_240_, v___x_241_, v_content_239_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_251_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = l_Lean_Doc_joinInlines(v_a_243_);
lean_dec(v_a_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_247_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_242_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_242_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
case 7:
{
lean_object* v_name_260_; lean_object* v_content_261_; size_t v_sz_262_; size_t v___x_263_; lean_object* v___x_264_; 
v_name_260_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_name_260_);
v_content_261_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_content_261_);
lean_dec_ref_known(v_x_57_, 2);
v_sz_262_ = lean_array_size(v_content_261_);
v___x_263_ = ((size_t)0ULL);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(v_x_56_, v_sz_262_, v___x_263_, v_content_261_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
v___x_266_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__14));
v___x_267_ = l_Lean_Doc_joinInlines(v_a_265_);
lean_dec(v_a_265_);
v___x_268_ = lean_array_to_list(v___x_267_);
v___x_269_ = l_String_intercalate(v___x_266_, v___x_268_);
lean_inc_ref(v_name_260_);
v___x_270_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_MarkdownM_addFootnote(v_name_260_, v___x_269_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_284_; 
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_285_);
v___x_272_ = v___x_270_;
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_270_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_274_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__15));
v___x_275_ = lean_string_append(v___x_274_, v_name_260_);
lean_dec_ref(v_name_260_);
v___x_276_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__16));
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_array_push(v___x_279_, v___x_277_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_280_);
v___x_282_ = v___x_272_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_name_260_);
v_a_286_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_270_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_270_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_name_260_);
v_a_294_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_264_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_264_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
case 8:
{
lean_object* v_alt_302_; lean_object* v_url_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec_ref(v_x_56_);
v_alt_302_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_alt_302_);
v_url_303_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_url_303_);
lean_dec_ref_known(v_x_57_, 2);
v___x_304_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__17));
v___x_305_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_302_);
lean_dec_ref(v_alt_302_);
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
lean_dec_ref(v___x_305_);
v___x_307_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__11));
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
v___x_309_ = lean_string_append(v___x_308_, v_url_303_);
lean_dec_ref(v_url_303_);
v___x_310_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__12));
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_mk_empty_array_with_capacity(v___x_312_);
v___x_314_ = lean_array_push(v___x_313_, v___x_311_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
case 9:
{
lean_object* v_content_316_; size_t v_sz_317_; size_t v___x_318_; lean_object* v___x_319_; 
v_content_316_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_content_316_);
lean_dec_ref_known(v_x_57_, 1);
v_sz_317_ = lean_array_size(v_content_316_);
v___x_318_ = ((size_t)0ULL);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(v_x_56_, v_sz_317_, v___x_318_, v_content_316_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_328_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_328_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = l_Lean_Doc_joinInlines(v_a_320_);
lean_dec(v_a_320_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
v_a_329_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_319_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_319_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
default: 
{
lean_object* v_container_337_; 
v_container_337_ = lean_ctor_get(v_x_57_, 0);
if (lean_obj_tag(v_container_337_) == 0)
{
lean_object* v_content_338_; lean_object* v_val_339_; lean_object* v___x_340_; size_t v_sz_341_; size_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_fallback_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc_ref(v_container_337_);
v_content_338_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref_n(v_content_338_, 2);
lean_dec_ref_known(v_x_57_, 2);
v_val_339_ = lean_ctor_get(v_container_337_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v_container_337_, 1);
lean_inc_ref_n(v_x_56_, 2);
v___x_340_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed), 6, 1);
lean_closure_set(v___x_340_, 0, v_x_56_);
v_sz_341_ = lean_array_size(v_content_338_);
v___x_342_ = ((size_t)0ULL);
v___x_343_ = lean_box_usize(v_sz_341_);
v___x_344_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed__const__1));
v_fallback_345_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___lam__0___boxed), 8, 4);
lean_closure_set(v_fallback_345_, 0, v_x_56_);
lean_closure_set(v_fallback_345_, 1, v___x_343_);
lean_closure_set(v_fallback_345_, 2, v___x_344_);
lean_closure_set(v_fallback_345_, 3, v_content_338_);
v___x_346_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_339_);
v___x_347_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineRendererForUnsafe(v___x_346_, v_a_59_, v_a_60_);
lean_dec(v___x_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
if (lean_obj_tag(v_a_348_) == 0)
{
lean_object* v___x_349_; 
lean_dec_ref(v_fallback_345_);
lean_dec_ref(v___x_340_);
lean_dec(v_val_339_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(v_x_56_, v_sz_341_, v___x_342_, v_content_338_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = l_Lean_Doc_joinInlines(v_a_350_);
lean_dec(v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_349_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_349_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v_val_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec_ref(v_x_56_);
v_val_367_ = lean_ctor_get(v_a_348_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v_a_348_, 1);
v___x_368_ = lean_apply_3(v_val_367_, v___x_340_, v_val_339_, v_content_338_);
v___x_369_ = l_Lean_Doc_withRendererFallback(v_fallback_345_, v___x_368_, v_a_58_, v_a_59_, v_a_60_);
return v___x_369_;
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v_fallback_345_);
lean_dec_ref(v___x_340_);
lean_dec(v_val_339_);
lean_dec_ref(v_content_338_);
lean_dec_ref(v_x_56_);
v_a_370_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_347_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_347_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v_content_378_; size_t v_sz_379_; size_t v___x_380_; lean_object* v___x_381_; 
v_content_378_ = lean_ctor_get(v_x_57_, 1);
lean_inc_ref(v_content_378_);
lean_dec_ref_known(v_x_57_, 2);
v_sz_379_ = lean_array_size(v_content_378_);
v___x_380_ = ((size_t)0ULL);
v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(v_x_56_, v_sz_379_, v___x_380_, v_content_378_, v_a_58_, v_a_59_, v_a_60_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = l_Lean_Doc_joinInlines(v_a_382_);
lean_dec(v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_381_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_381_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
v___jp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = l_Lean_Doc_joinInlines(v_pieces_63_);
lean_dec_ref(v_pieces_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = l_Lean_Doc_joinInlines(v_pieces_67_);
lean_dec_ref(v_pieces_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(lean_object* v_x_399_, size_t v_sz_400_, size_t v_i_401_, lean_object* v_bs_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_lt(v_i_401_, v_sz_400_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec_ref(v_x_399_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v_bs_402_);
return v___x_408_;
}
else
{
lean_object* v_v_409_; lean_object* v___x_410_; lean_object* v_bs_x27_411_; lean_object* v___x_412_; 
v_v_409_ = lean_array_uget(v_bs_402_, v_i_401_);
v___x_410_ = lean_unsigned_to_nat(0u);
v_bs_x27_411_ = lean_array_uset(v_bs_402_, v_i_401_, v___x_410_);
lean_inc_ref(v_x_399_);
v___x_412_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(v_x_399_, v_v_409_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_401_, v___x_414_);
v___x_416_ = lean_array_uset(v_bs_x27_411_, v_i_401_, v_a_413_);
v_i_401_ = v___x_415_;
v_bs_402_ = v___x_416_;
goto _start;
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_bs_x27_411_);
lean_dec_ref(v_x_399_);
v_a_418_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_412_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_412_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___lam__0(lean_object* v_x_426_, size_t v_sz_427_, size_t v___x_428_, lean_object* v_content_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(v_x_426_, v_sz_427_, v___x_428_, v_content_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_443_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = l_Lean_Doc_joinInlines(v_a_435_);
lean_dec(v_a_435_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_434_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_434_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8___boxed(lean_object* v_x_452_, lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_bs_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
size_t v_sz_boxed_460_; size_t v_i_boxed_461_; lean_object* v_res_462_; 
v_sz_boxed_460_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_461_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5_spec__8(v_x_452_, v_sz_boxed_460_, v_i_boxed_461_, v_bs_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__12(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_zero_465_; uint8_t v_isZero_466_; 
v_zero_465_ = lean_unsigned_to_nat(0u);
v_isZero_466_ = lean_nat_dec_eq(v_x_463_, v_zero_465_);
if (v_isZero_466_ == 1)
{
lean_dec(v_x_463_);
return v_x_464_;
}
else
{
uint32_t v___x_467_; lean_object* v_one_468_; lean_object* v_n_469_; lean_object* v___x_470_; 
v___x_467_ = 32;
v_one_468_ = lean_unsigned_to_nat(1u);
v_n_469_ = lean_nat_sub(v_x_463_, v_one_468_);
lean_dec(v_x_463_);
v___x_470_ = lean_string_push(v_x_464_, v___x_467_);
v_x_463_ = v_n_469_;
v_x_464_ = v___x_470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11(size_t v_sz_476_, size_t v_i_477_, lean_object* v_bs_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_477_, v_sz_476_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v_bs_478_);
return v___x_484_;
}
else
{
lean_object* v_v_485_; lean_object* v___x_486_; lean_object* v_bs_x27_487_; size_t v_sz_488_; size_t v___x_489_; lean_object* v___x_490_; 
v_v_485_ = lean_array_uget(v_bs_478_, v_i_477_);
v___x_486_ = lean_unsigned_to_nat(0u);
v_bs_x27_487_ = lean_array_uset(v_bs_478_, v_i_477_, v___x_486_);
v_sz_488_ = lean_array_size(v_v_485_);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_488_, v___x_489_, v_v_485_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__0));
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__1));
v___x_494_ = l_Lean_Doc_joinBlocks(v_a_491_);
lean_dec(v_a_491_);
v___x_495_ = l_Lean_Doc_prefixListLines(v___x_492_, v___x_493_, v___x_494_);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_477_, v___x_496_);
v___x_498_ = lean_array_uset(v_bs_x27_487_, v_i_477_, v___x_495_);
v_i_477_ = v___x_497_;
v_bs_478_ = v___x_498_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_487_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13(lean_object* v_as_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v_b_504_);
return v___x_510_;
}
else
{
lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_546_; 
v_fst_511_ = lean_ctor_get(v_b_504_, 0);
v_snd_512_ = lean_ctor_get(v_b_504_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_b_504_);
if (v_isSharedCheck_546_ == 0)
{
v___x_514_ = v_b_504_;
v_isShared_515_ = v_isSharedCheck_546_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_inc(v_fst_511_);
lean_dec(v_b_504_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_546_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; size_t v_sz_524_; size_t v___x_525_; lean_object* v___x_526_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v_a_517_ = lean_array_uget_borrowed(v_as_501_, v_i_503_);
lean_inc(v_snd_512_);
v___x_518_ = l_Nat_reprFast(v_snd_512_);
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13___closed__0));
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
v___x_521_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7));
v___x_522_ = lean_string_utf8_byte_size(v___x_520_);
v___x_523_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__12(v___x_522_, v___x_521_);
v_sz_524_ = lean_array_size(v_a_517_);
v___x_525_ = ((size_t)0ULL);
lean_inc(v_a_517_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_524_, v___x_525_, v_a_517_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_Lean_Doc_joinBlocks(v_a_527_);
lean_dec(v_a_527_);
v___x_529_ = l_Lean_Doc_prefixListLines(v___x_520_, v___x_523_, v___x_528_);
v___x_530_ = lean_array_push(v_fst_511_, v___x_529_);
v___x_531_ = lean_nat_add(v_snd_512_, v___x_516_);
lean_dec(v_snd_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_531_);
lean_ctor_set(v___x_514_, 0, v___x_530_);
v___x_533_ = v___x_514_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
size_t v___x_534_; size_t v___x_535_; 
v___x_534_ = ((size_t)1ULL);
v___x_535_ = lean_usize_add(v_i_503_, v___x_534_);
v_i_503_ = v___x_535_;
v_b_504_ = v___x_533_;
goto _start;
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v___x_523_);
lean_dec_ref(v___x_520_);
lean_del_object(v___x_514_);
lean_dec(v_snd_512_);
lean_dec(v_fst_511_);
v_a_538_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_526_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_526_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14(size_t v_sz_552_, size_t v_i_553_, lean_object* v_bs_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_lt(v_i_553_, v_sz_552_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_bs_554_);
return v___x_560_;
}
else
{
lean_object* v_v_561_; lean_object* v___x_562_; lean_object* v_term_563_; lean_object* v_desc_564_; lean_object* v___x_565_; lean_object* v_bs_x27_566_; lean_object* v_a_568_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_v_561_ = lean_array_uget_borrowed(v_bs_554_, v_i_553_);
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__0));
v_term_563_ = lean_ctor_get(v_v_561_, 0);
lean_inc_ref(v_term_563_);
v_desc_564_ = lean_ctor_get(v_v_561_, 1);
lean_inc_ref(v_desc_564_);
v___x_565_ = lean_unsigned_to_nat(0u);
v_bs_x27_566_ = lean_array_uset(v_bs_554_, v_i_553_, v___x_565_);
v___x_573_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_573_, 0, v_term_563_);
v___x_574_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(v___x_562_, v___x_573_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; size_t v_sz_576_; size_t v___x_577_; lean_object* v___x_578_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v_sz_576_ = lean_array_size(v_desc_564_);
v___x_577_ = ((size_t)0ULL);
lean_inc_ref(v_desc_564_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_576_, v___x_577_, v_desc_564_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___y_581_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_mk_empty_array_with_capacity(v___x_585_);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__2));
v___x_588_ = lean_unsigned_to_nat(2u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
v___x_590_ = lean_array_push(v___x_589_, v_a_575_);
v___x_591_ = lean_array_push(v___x_590_, v___x_587_);
v___x_592_ = l_Lean_Doc_joinInlines(v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = lean_array_get_size(v_desc_564_);
lean_dec_ref(v_desc_564_);
v___x_594_ = lean_nat_dec_le(v___x_593_, v___x_585_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_array_push(v___x_586_, v___x_592_);
v___x_596_ = l_Array_append___redArg(v___x_595_, v_a_579_);
lean_dec(v_a_579_);
v___x_597_ = l_Lean_Doc_joinBlocks(v___x_596_);
lean_dec_ref(v___x_596_);
v___y_581_ = v___x_597_;
goto v___jp_580_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec_ref(v___x_586_);
v___x_598_ = l_Lean_Doc_joinBlocks(v_a_579_);
lean_dec(v_a_579_);
v___x_599_ = l_Array_append___redArg(v___x_592_, v___x_598_);
lean_dec_ref(v___x_598_);
v___y_581_ = v___x_599_;
goto v___jp_580_;
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__0));
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___closed__1));
v___x_584_ = l_Lean_Doc_prefixListLines(v___x_582_, v___x_583_, v___y_581_);
v_a_568_ = v___x_584_;
goto v___jp_567_;
}
}
else
{
lean_dec(v_a_575_);
lean_dec_ref(v_bs_x27_566_);
lean_dec_ref(v_desc_564_);
return v___x_578_;
}
}
else
{
lean_dec_ref(v_desc_564_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_600_; 
v_a_600_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_574_, 1);
v_a_568_ = v_a_600_;
goto v___jp_567_;
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_bs_x27_566_);
v_a_601_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_574_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_574_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
v___jp_567_:
{
size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_553_, v___x_569_);
v___x_571_ = lean_array_uset(v_bs_x27_566_, v_i_553_, v_a_568_);
v_i_553_ = v___x_570_;
v_bs_554_ = v___x_571_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___boxed(lean_object* v_x_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_x_612_, v_a_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___lam__0___boxed(lean_object* v_sz_618_, lean_object* v___x_619_, lean_object* v_content_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
size_t v_sz_boxed_625_; size_t v___x_12815__boxed_626_; lean_object* v_res_627_; 
v_sz_boxed_625_ = lean_unbox_usize(v_sz_618_);
lean_dec(v_sz_618_);
v___x_12815__boxed_626_ = lean_unbox_usize(v___x_619_);
lean_dec(v___x_619_);
v_res_627_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___lam__0(v_sz_boxed_625_, v___x_12815__boxed_626_, v_content_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(lean_object* v_x_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
switch(lean_obj_tag(v_x_628_))
{
case 0:
{
lean_object* v_contents_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_642_; 
v_contents_633_ = lean_ctor_get(v_x_628_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_642_ == 0)
{
v___x_635_ = v_x_628_;
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_contents_633_);
lean_dec(v_x_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__0));
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 9);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_contents_633_);
v___x_639_ = v_reuseFailAlloc_641_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(v___x_637_, v___x_639_, v_a_629_, v_a_630_, v_a_631_);
return v___x_640_;
}
}
}
case 1:
{
lean_object* v_content_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_content_643_ = lean_ctor_get(v_x_628_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v_x_628_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_content_643_);
lean_dec(v_x_628_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
case 2:
{
lean_object* v_items_652_; size_t v_sz_653_; size_t v___x_654_; lean_object* v___x_655_; 
v_items_652_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_items_652_);
lean_dec_ref_known(v_x_628_, 1);
v_sz_653_ = lean_array_size(v_items_652_);
v___x_654_ = ((size_t)0ULL);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11(v_sz_653_, v___x_654_, v_items_652_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_Doc_joinBlocks(v_a_656_);
lean_dec(v_a_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_a_665_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_655_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_655_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
case 3:
{
lean_object* v_start_673_; lean_object* v_items_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_708_; 
v_start_673_ = lean_ctor_get(v_x_628_, 0);
v_items_674_ = lean_ctor_get(v_x_628_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_708_ == 0)
{
v___x_676_ = v_x_628_;
v_isShared_677_ = v_isSharedCheck_708_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_items_674_);
lean_inc(v_start_673_);
lean_dec(v_x_628_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_708_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_out_678_; lean_object* v___y_680_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_out_678_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__2));
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = l_Int_toNat(v_start_673_);
lean_dec(v_start_673_);
v___x_707_ = lean_nat_dec_le(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec(v___x_706_);
v___y_680_ = v___x_705_;
goto v___jp_679_;
}
else
{
v___y_680_ = v___x_706_;
goto v___jp_679_;
}
v___jp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
lean_ctor_set(v___x_676_, 1, v___y_680_);
lean_ctor_set(v___x_676_, 0, v_out_678_);
v___x_682_ = v___x_676_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_out_678_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___y_680_);
v___x_682_ = v_reuseFailAlloc_704_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
size_t v_sz_683_; size_t v___x_684_; lean_object* v___x_685_; 
v_sz_683_ = lean_array_size(v_items_674_);
v___x_684_ = ((size_t)0ULL);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13(v_items_674_, v_sz_683_, v___x_684_, v___x_682_, v_a_629_, v_a_630_, v_a_631_);
lean_dec_ref(v_items_674_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v_fst_690_ = lean_ctor_get(v_a_686_, 0);
lean_inc(v_fst_690_);
lean_dec(v_a_686_);
v___x_691_ = l_Lean_Doc_joinBlocks(v_fst_690_);
lean_dec(v_fst_690_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_685_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_685_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_items_709_; size_t v_sz_710_; size_t v___x_711_; lean_object* v___x_712_; 
v_items_709_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_items_709_);
lean_dec_ref_known(v_x_628_, 1);
v_sz_710_ = lean_array_size(v_items_709_);
v___x_711_ = ((size_t)0ULL);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14(v_sz_710_, v___x_711_, v_items_709_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_721_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l_Lean_Doc_joinBlocks(v_a_713_);
lean_dec(v_a_713_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_712_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_712_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
case 5:
{
lean_object* v_items_730_; size_t v_sz_731_; size_t v___x_732_; lean_object* v___x_733_; 
v_items_730_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_items_730_);
lean_dec_ref_known(v_x_628_, 1);
v_sz_731_ = lean_array_size(v_items_730_);
v___x_732_ = ((size_t)0ULL);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_731_, v___x_732_, v_items_730_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_744_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_744_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_744_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_738_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___closed__0));
v___x_739_ = l_Lean_Doc_joinBlocks(v_a_734_);
lean_dec(v_a_734_);
v___x_740_ = l_Lean_Doc_prefixLines(v___x_738_, v___x_739_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_740_);
v___x_742_ = v___x_736_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_a_745_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_733_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_733_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
case 6:
{
lean_object* v_content_753_; size_t v_sz_754_; size_t v___x_755_; lean_object* v___x_756_; 
v_content_753_ = lean_ctor_get(v_x_628_, 0);
lean_inc_ref(v_content_753_);
lean_dec_ref_known(v_x_628_, 1);
v_sz_754_ = lean_array_size(v_content_753_);
v___x_755_ = ((size_t)0ULL);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_754_, v___x_755_, v_content_753_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_765_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = l_Lean_Doc_joinBlocks(v_a_757_);
lean_dec(v_a_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_756_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_756_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
default: 
{
lean_object* v_container_774_; 
v_container_774_ = lean_ctor_get(v_x_628_, 0);
if (lean_obj_tag(v_container_774_) == 0)
{
lean_object* v_content_775_; lean_object* v_val_776_; lean_object* v___x_777_; lean_object* v___x_778_; size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v_fallback_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_inc_ref(v_container_774_);
v_content_775_ = lean_ctor_get(v_x_628_, 1);
lean_inc_ref_n(v_content_775_, 2);
lean_dec_ref_known(v_x_628_, 2);
v_val_776_ = lean_ctor_get(v_container_774_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v_container_774_, 1);
v___x_777_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___closed__1));
v___x_778_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___boxed), 5, 0);
v_sz_779_ = lean_array_size(v_content_775_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_box_usize(v_sz_779_);
v___x_782_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___boxed__const__1));
v_fallback_783_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___lam__0___boxed), 7, 3);
lean_closure_set(v_fallback_783_, 0, v___x_781_);
lean_closure_set(v_fallback_783_, 1, v___x_782_);
lean_closure_set(v_fallback_783_, 2, v_content_775_);
v___x_784_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_776_);
v___x_785_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockRendererForUnsafe(v___x_784_, v_a_630_, v_a_631_);
lean_dec(v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
if (lean_obj_tag(v_a_786_) == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v_fallback_783_);
lean_dec_ref(v___x_778_);
lean_dec(v_val_776_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_779_, v___x_780_, v_content_775_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = l_Lean_Doc_joinBlocks(v_a_788_);
lean_dec(v_a_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_787_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_787_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_val_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_val_805_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_a_786_, 1);
v___x_806_ = lean_apply_4(v_val_805_, v___x_777_, v___x_778_, v_val_776_, v_content_775_);
v___x_807_ = l_Lean_Doc_withRendererFallback(v_fallback_783_, v___x_806_, v_a_629_, v_a_630_, v_a_631_);
return v___x_807_;
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_fallback_783_);
lean_dec_ref(v___x_778_);
lean_dec(v_val_776_);
lean_dec_ref(v_content_775_);
v_a_808_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_785_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_785_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_content_816_; size_t v_sz_817_; size_t v___x_818_; lean_object* v___x_819_; 
v_content_816_ = lean_ctor_get(v_x_628_, 1);
lean_inc_ref(v_content_816_);
lean_dec_ref_known(v_x_628_, 2);
v_sz_817_ = lean_array_size(v_content_816_);
v___x_818_ = ((size_t)0ULL);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_817_, v___x_818_, v_content_816_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_828_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_828_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = l_Lean_Doc_joinBlocks(v_a_820_);
lean_dec(v_a_820_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_819_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(size_t v_sz_837_, size_t v_i_838_, lean_object* v_bs_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v___x_844_; 
v___x_844_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v_bs_839_);
return v___x_845_;
}
else
{
lean_object* v_v_846_; lean_object* v___x_847_; lean_object* v_bs_x27_848_; lean_object* v___x_849_; 
v_v_846_ = lean_array_uget(v_bs_839_, v_i_838_);
v___x_847_ = lean_unsigned_to_nat(0u);
v_bs_x27_848_ = lean_array_uset(v_bs_839_, v_i_838_, v___x_847_);
v___x_849_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_v_846_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_838_, v___x_851_);
v___x_853_ = lean_array_uset(v_bs_x27_848_, v_i_838_, v_a_850_);
v_i_838_ = v___x_852_;
v_bs_839_ = v___x_853_;
goto _start;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_bs_x27_848_);
v_a_855_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_849_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_849_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3___lam__0(size_t v_sz_863_, size_t v___x_864_, lean_object* v_content_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_863_, v___x_864_, v_content_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_879_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_879_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = l_Lean_Doc_joinBlocks(v_a_871_);
lean_dec(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_870_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_870_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10___boxed(lean_object* v_sz_888_, lean_object* v_i_889_, lean_object* v_bs_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_888_);
lean_dec(v_sz_888_);
v_i_boxed_896_ = lean_unbox_usize(v_i_889_);
lean_dec(v_i_889_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__10(v_sz_boxed_895_, v_i_boxed_896_, v_bs_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11___boxed(lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_bs_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
size_t v_sz_boxed_905_; size_t v_i_boxed_906_; lean_object* v_res_907_; 
v_sz_boxed_905_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_906_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__11(v_sz_boxed_905_, v_i_boxed_906_, v_bs_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13___boxed(lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
size_t v_sz_boxed_916_; size_t v_i_boxed_917_; lean_object* v_res_918_; 
v_sz_boxed_916_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_917_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__13(v_as_908_, v_sz_boxed_916_, v_i_boxed_917_, v_b_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v_as_908_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___boxed(lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_bs_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_sz_boxed_926_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_927_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14(v_sz_boxed_926_, v_i_boxed_927_, v_bs_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(size_t v_sz_929_, size_t v_i_930_, lean_object* v_bs_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_lt(v_i_930_, v_sz_929_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_bs_931_);
return v___x_937_;
}
else
{
lean_object* v_v_938_; lean_object* v___x_939_; lean_object* v_bs_x27_940_; lean_object* v___x_941_; 
v_v_938_ = lean_array_uget(v_bs_931_, v_i_930_);
v___x_939_ = lean_unsigned_to_nat(0u);
v_bs_x27_940_ = lean_array_uset(v_bs_931_, v_i_930_, v___x_939_);
v___x_941_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3(v_v_938_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_add(v_i_930_, v___x_943_);
v___x_945_ = lean_array_uset(v_bs_x27_940_, v_i_930_, v_a_942_);
v_i_930_ = v___x_944_;
v_bs_931_ = v___x_945_;
goto _start;
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v_bs_x27_940_);
v_a_947_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_941_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_941_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4___boxed(lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_bs_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v_sz_boxed_962_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_963_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_boxed_962_, v_i_boxed_963_, v_bs_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__6(size_t v_sz_965_, size_t v_i_966_, lean_object* v_bs_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___x_972_; 
v___x_972_ = lean_usize_dec_lt(v_i_966_, v_sz_965_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_bs_967_);
return v___x_973_;
}
else
{
lean_object* v_v_974_; lean_object* v___x_975_; lean_object* v_bs_x27_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_v_974_ = lean_array_uget(v_bs_967_, v_i_966_);
v___x_975_ = lean_unsigned_to_nat(0u);
v_bs_x27_976_ = lean_array_uset(v_bs_967_, v_i_966_, v___x_975_);
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__3_spec__14___closed__0));
v___x_978_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5(v___x_977_, v_v_974_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_add(v_i_966_, v___x_980_);
v___x_982_ = lean_array_uset(v_bs_x27_976_, v_i_966_, v_a_979_);
v_i_966_ = v___x_981_;
v_bs_967_ = v___x_982_;
goto _start;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_bs_x27_976_);
v_a_984_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_978_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_978_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__6___boxed(lean_object* v_sz_992_, lean_object* v_i_993_, lean_object* v_bs_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
size_t v_sz_boxed_999_; size_t v_i_boxed_1000_; lean_object* v_res_1001_; 
v_sz_boxed_999_ = lean_unbox_usize(v_sz_992_);
lean_dec(v_sz_992_);
v_i_boxed_1000_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_res_1001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__6(v_sz_boxed_999_, v_i_boxed_1000_, v_bs_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v_zero_1004_; uint8_t v_isZero_1005_; 
v_zero_1004_ = lean_unsigned_to_nat(0u);
v_isZero_1005_ = lean_nat_dec_eq(v_x_1002_, v_zero_1004_);
if (v_isZero_1005_ == 1)
{
lean_dec(v_x_1002_);
return v_x_1003_;
}
else
{
uint32_t v___x_1006_; lean_object* v_one_1007_; lean_object* v_n_1008_; lean_object* v___x_1009_; 
v___x_1006_ = 35;
v_one_1007_ = lean_unsigned_to_nat(1u);
v_n_1008_ = lean_nat_sub(v_x_1002_, v_one_1007_);
lean_dec(v_x_1002_);
v___x_1009_ = lean_string_push(v_x_1003_, v___x_1006_);
v_x_1002_ = v_n_1008_;
v_x_1003_ = v___x_1009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg(lean_object* v_level_1012_, lean_object* v_part_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_title_1018_; lean_object* v_content_1019_; lean_object* v_subParts_1020_; size_t v_sz_1021_; size_t v___x_1022_; lean_object* v___x_1023_; 
v_title_1018_ = lean_ctor_get(v_part_1013_, 0);
lean_inc_ref(v_title_1018_);
v_content_1019_ = lean_ctor_get(v_part_1013_, 3);
lean_inc_ref(v_content_1019_);
v_subParts_1020_ = lean_ctor_get(v_part_1013_, 4);
lean_inc_ref(v_subParts_1020_);
lean_dec_ref(v_part_1013_);
v_sz_1021_ = lean_array_size(v_title_1018_);
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__6(v_sz_1021_, v___x_1022_, v_title_1018_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; size_t v_sz_1036_; lean_object* v___x_1037_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7));
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_level_1012_, v___x_1026_);
lean_inc(v___x_1027_);
v___x_1028_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__7(v___x_1027_, v___x_1025_);
v___x_1029_ = ((lean_object*)(l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg___closed__0));
v___x_1030_ = lean_string_append(v___x_1028_, v___x_1029_);
v___x_1031_ = lean_mk_empty_array_with_capacity(v___x_1026_);
lean_inc_ref_n(v___x_1031_, 2);
v___x_1032_ = lean_array_push(v___x_1031_, v___x_1030_);
v___x_1033_ = lean_array_push(v___x_1031_, v___x_1032_);
v___x_1034_ = l_Array_append___redArg(v___x_1033_, v_a_1024_);
lean_dec(v_a_1024_);
v___x_1035_ = l_Lean_Doc_joinInlines(v___x_1034_);
lean_dec_ref(v___x_1034_);
v_sz_1036_ = lean_array_size(v_content_1019_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_1036_, v___x_1022_, v_content_1019_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; size_t v_sz_1039_; lean_object* v___x_1040_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v_sz_1039_ = lean_array_size(v_subParts_1020_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___redArg(v___x_1027_, v_sz_1039_, v___x_1022_, v_subParts_1020_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v___x_1027_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1052_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1052_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1045_ = lean_array_push(v___x_1031_, v___x_1035_);
v___x_1046_ = l_Array_append___redArg(v___x_1045_, v_a_1038_);
lean_dec(v_a_1038_);
v___x_1047_ = l_Array_append___redArg(v___x_1046_, v_a_1041_);
lean_dec(v_a_1041_);
v___x_1048_ = l_Lean_Doc_joinBlocks(v___x_1047_);
lean_dec_ref(v___x_1047_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1048_);
v___x_1050_ = v___x_1043_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_a_1038_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1031_);
v_a_1053_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1040_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1040_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1031_);
lean_dec(v___x_1027_);
lean_dec_ref(v_subParts_1020_);
v_a_1061_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1037_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1037_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v_subParts_1020_);
lean_dec_ref(v_content_1019_);
v_a_1069_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1023_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1023_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___redArg(lean_object* v___x_1077_, size_t v_sz_1078_, size_t v_i_1079_, lean_object* v_bs_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_usize_dec_lt(v_i_1079_, v_sz_1078_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_bs_1080_);
return v___x_1086_;
}
else
{
lean_object* v_v_1087_; lean_object* v___x_1088_; lean_object* v_bs_x27_1089_; lean_object* v___x_1090_; 
v_v_1087_ = lean_array_uget(v_bs_1080_, v_i_1079_);
v___x_1088_ = lean_unsigned_to_nat(0u);
v_bs_x27_1089_ = lean_array_uset(v_bs_1080_, v_i_1079_, v___x_1088_);
v___x_1090_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg(v___x_1077_, v_v_1087_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_add(v_i_1079_, v___x_1092_);
v___x_1094_ = lean_array_uset(v_bs_x27_1089_, v_i_1079_, v_a_1091_);
v_i_1079_ = v___x_1093_;
v_bs_1080_ = v___x_1094_;
goto _start;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_bs_x27_1089_);
v_a_1096_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1090_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1090_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___redArg___boxed(lean_object* v___x_1104_, lean_object* v_sz_1105_, lean_object* v_i_1106_, lean_object* v_bs_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
size_t v_sz_boxed_1112_; size_t v_i_boxed_1113_; lean_object* v_res_1114_; 
v_sz_boxed_1112_ = lean_unbox_usize(v_sz_1105_);
lean_dec(v_sz_1105_);
v_i_boxed_1113_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_res_1114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___redArg(v___x_1104_, v_sz_boxed_1112_, v_i_boxed_1113_, v_bs_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___x_1104_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg___boxed(lean_object* v_level_1115_, lean_object* v_part_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg(v_level_1115_, v_part_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec(v_level_1115_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__5(size_t v_sz_1122_, size_t v_i_1123_, lean_object* v_bs_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_usize_dec_lt(v_i_1123_, v_sz_1122_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_bs_1124_);
return v___x_1130_;
}
else
{
lean_object* v_v_1131_; lean_object* v___x_1132_; lean_object* v_bs_x27_1133_; lean_object* v___x_1134_; 
v_v_1131_ = lean_array_uget(v_bs_1124_, v_i_1123_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v_bs_x27_1133_ = lean_array_uset(v_bs_1124_, v_i_1123_, v___x_1132_);
v___x_1134_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg(v___x_1132_, v_v_1131_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_add(v_i_1123_, v___x_1136_);
v___x_1138_ = lean_array_uset(v_bs_x27_1133_, v_i_1123_, v_a_1135_);
v_i_1123_ = v___x_1137_;
v_bs_1124_ = v___x_1138_;
goto _start;
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_bs_x27_1133_);
v_a_1140_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1134_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1134_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__5___boxed(lean_object* v_sz_1148_, lean_object* v_i_1149_, lean_object* v_bs_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1148_);
lean_dec(v_sz_1148_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1149_);
lean_dec(v_i_1149_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__5(v_sz_boxed_1155_, v_i_boxed_1156_, v_bs_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(lean_object* v_fst_1158_, lean_object* v_snd_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
v_sz_1164_ = lean_array_size(v_fst_1158_);
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__4(v_sz_1164_, v___x_1165_, v_fst_1158_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; size_t v_sz_1168_; lean_object* v___x_1169_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v_sz_1168_ = lean_array_size(v_snd_1159_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__5(v_sz_1168_, v___x_1165_, v_snd_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1179_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1179_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1179_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = l_Array_append___redArg(v_a_1167_, v_a_1170_);
lean_dec(v_a_1170_);
v___x_1175_ = l_Lean_Doc_joinBlocks(v___x_1174_);
lean_dec_ref(v___x_1174_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1175_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1167_);
v_a_1180_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1169_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1169_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_snd_1159_);
v_a_1188_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1166_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1166_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed(lean_object* v_fst_1196_, lean_object* v_snd_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0(v_fst_1196_, v_snd_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
lean_ctor_set(v___x_1208_, 2, v___x_1207_);
lean_ctor_set(v___x_1208_, 3, v___x_1207_);
lean_ctor_set(v___x_1208_, 4, v___x_1206_);
lean_ctor_set(v___x_1208_, 5, v___x_1206_);
lean_ctor_set(v___x_1208_, 6, v___x_1206_);
lean_ctor_set(v___x_1208_, 7, v___x_1206_);
lean_ctor_set(v___x_1208_, 8, v___x_1206_);
lean_ctor_set(v___x_1208_, 9, v___x_1206_);
lean_ctor_set(v___x_1208_, 10, v___x_1206_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(32u);
v___x_1210_ = lean_mk_empty_array_with_capacity(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((size_t)5ULL);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_unsigned_to_nat(32u);
v___x_1215_ = lean_mk_empty_array_with_capacity(v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__3);
v___x_1217_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1215_);
lean_ctor_set(v___x_1217_, 2, v___x_1213_);
lean_ctor_set(v___x_1217_, 3, v___x_1213_);
lean_ctor_set_usize(v___x_1217_, 4, v___x_1212_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_box(1);
v___x_1219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4);
v___x_1220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__1);
v___x_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1219_);
lean_ctor_set(v___x_1221_, 2, v___x_1218_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg(lean_object* v_msgData_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v_env_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_scopes_1229_; lean_object* v___x_1230_; lean_object* v_opts_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1225_ = lean_st_ref_get(v___y_1223_);
v_env_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_ref(v_env_1226_);
lean_dec(v___x_1225_);
v___x_1227_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1228_ = lean_st_ref_get(v___y_1223_);
v_scopes_1229_ = lean_ctor_get(v___x_1228_, 2);
lean_inc(v_scopes_1229_);
lean_dec(v___x_1228_);
v___x_1230_ = l_List_head_x21___redArg(v___x_1227_, v_scopes_1229_);
lean_dec(v_scopes_1229_);
v_opts_1231_ = lean_ctor_get(v___x_1230_, 1);
lean_inc_ref(v_opts_1231_);
lean_dec(v___x_1230_);
v___x_1232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__2);
v___x_1233_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__5);
v___x_1234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1234_, 0, v_env_1226_);
lean_ctor_set(v___x_1234_, 1, v___x_1232_);
lean_ctor_set(v___x_1234_, 2, v___x_1233_);
lean_ctor_set(v___x_1234_, 3, v_opts_1231_);
v___x_1235_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v_msgData_1222_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg(v_msgData_1237_, v___y_1238_);
lean_dec(v___y_1238_);
return v_res_1240_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_box(1);
v___x_1242_ = l_Lean_MessageData_ofFormat(v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__3(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__2));
v___x_1247_ = l_Lean_MessageData_ofFormat(v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11(lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1249_) == 0)
{
return v_x_1248_;
}
else
{
lean_object* v_head_1250_; lean_object* v_tail_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1273_; 
v_head_1250_ = lean_ctor_get(v_x_1249_, 0);
v_tail_1251_ = lean_ctor_get(v_x_1249_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1249_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1253_ = v_x_1249_;
v_isShared_1254_ = v_isSharedCheck_1273_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_tail_1251_);
lean_inc(v_head_1250_);
lean_dec(v_x_1249_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1273_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_before_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1271_; 
v_before_1255_ = lean_ctor_get(v_head_1250_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_head_1250_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_head_1250_, 1);
lean_dec(v_unused_1272_);
v___x_1257_ = v_head_1250_;
v_isShared_1258_ = v_isSharedCheck_1271_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_before_1255_);
lean_dec(v_head_1250_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1271_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0);
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 7);
lean_ctor_set(v___x_1257_, 1, v___x_1259_);
lean_ctor_set(v___x_1257_, 0, v_x_1248_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_x_1248_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__3);
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 7);
lean_ctor_set(v___x_1253_, 1, v___x_1262_);
lean_ctor_set(v___x_1253_, 0, v___x_1261_);
v___x_1264_ = v___x_1253_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = l_Lean_MessageData_ofSyntax(v_before_1255_);
v___x_1266_ = l_Lean_indentD(v___x_1265_);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1264_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v_x_1248_ = v___x_1267_;
v_x_1249_ = v_tail_1251_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__10(lean_object* v_opts_1274_, lean_object* v_opt_1275_){
_start:
{
lean_object* v_name_1276_; lean_object* v_defValue_1277_; lean_object* v_map_1278_; lean_object* v___x_1279_; 
v_name_1276_ = lean_ctor_get(v_opt_1275_, 0);
v_defValue_1277_ = lean_ctor_get(v_opt_1275_, 1);
v_map_1278_ = lean_ctor_get(v_opts_1274_, 0);
v___x_1279_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1278_, v_name_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_unbox(v_defValue_1277_);
return v___x_1280_;
}
else
{
lean_object* v_val_1281_; 
v_val_1281_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1279_, 1);
if (lean_obj_tag(v_val_1281_) == 1)
{
uint8_t v_v_1282_; 
v_v_1282_ = lean_ctor_get_uint8(v_val_1281_, 0);
lean_dec_ref_known(v_val_1281_, 0);
return v_v_1282_;
}
else
{
uint8_t v___x_1283_; 
lean_dec(v_val_1281_);
v___x_1283_ = lean_unbox(v_defValue_1277_);
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_opts_1284_, lean_object* v_opt_1285_){
_start:
{
uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__10(v_opts_1284_, v_opt_1285_);
lean_dec_ref(v_opt_1285_);
lean_dec_ref(v_opts_1284_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__1));
v___x_1292_ = l_Lean_MessageData_ofFormat(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg(lean_object* v_msgData_1293_, lean_object* v_macroStack_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_scopes_1299_; lean_object* v___x_1300_; lean_object* v_opts_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1297_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1298_ = lean_st_ref_get(v___y_1295_);
v_scopes_1299_ = lean_ctor_get(v___x_1298_, 2);
lean_inc(v_scopes_1299_);
lean_dec(v___x_1298_);
v___x_1300_ = l_List_head_x21___redArg(v___x_1297_, v_scopes_1299_);
lean_dec(v_scopes_1299_);
v_opts_1301_ = lean_ctor_get(v___x_1300_, 1);
lean_inc_ref(v_opts_1301_);
lean_dec(v___x_1300_);
v___x_1302_ = l_Lean_Elab_pp_macroStack;
v___x_1303_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__10(v_opts_1301_, v___x_1302_);
lean_dec_ref(v_opts_1301_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec(v_macroStack_1294_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_msgData_1293_);
return v___x_1304_;
}
else
{
if (lean_obj_tag(v_macroStack_1294_) == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_msgData_1293_);
return v___x_1305_;
}
else
{
lean_object* v_head_1306_; lean_object* v_after_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1322_; 
v_head_1306_ = lean_ctor_get(v_macroStack_1294_, 0);
lean_inc(v_head_1306_);
v_after_1307_ = lean_ctor_get(v_head_1306_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_head_1306_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_head_1306_, 0);
lean_dec(v_unused_1323_);
v___x_1309_ = v_head_1306_;
v_isShared_1310_ = v_isSharedCheck_1322_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_after_1307_);
lean_dec(v_head_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1322_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0);
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 7);
lean_ctor_set(v___x_1309_, 1, v___x_1311_);
lean_ctor_set(v___x_1309_, 0, v_msgData_1293_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_msgData_1293_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_msgData_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1314_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___closed__2);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_MessageData_ofSyntax(v_after_1307_);
v___x_1317_ = l_Lean_indentD(v___x_1316_);
v_msgData_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1318_, 0, v___x_1315_);
lean_ctor_set(v_msgData_1318_, 1, v___x_1317_);
v___x_1319_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11(v_msgData_1318_, v_macroStack_1294_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_1324_, lean_object* v_macroStack_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg(v_msgData_1324_, v_macroStack_1325_, v___y_1326_);
lean_dec(v___y_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(lean_object* v_msg_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Elab_Command_getRef___redArg(v___y_1330_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_macroStack_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1348_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v_macroStack_1335_ = lean_ctor_get(v___y_1330_, 4);
v___x_1336_ = l_Lean_Elab_getBetterRef(v_a_1334_, v_macroStack_1335_);
lean_dec(v_a_1334_);
v___x_1337_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg(v_msg_1329_, v___y_1331_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
lean_inc(v_macroStack_1335_);
v___x_1339_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg(v_a_1338_, v_macroStack_1335_, v___y_1331_);
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1348_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1336_);
lean_ctor_set(v___x_1344_, 1, v_a_1340_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 1);
lean_ctor_set(v___x_1342_, 0, v___x_1344_);
v___x_1346_ = v___x_1342_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_msg_1329_);
v_a_1349_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1333_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1333_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg___boxed(lean_object* v_msg_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v_msg_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0(uint8_t v_suppressElabErrors_1363_, uint8_t v___x_1364_, lean_object* v_x_1365_){
_start:
{
if (lean_obj_tag(v_x_1365_) == 1)
{
lean_object* v_pre_1366_; 
v_pre_1366_ = lean_ctor_get(v_x_1365_, 0);
if (lean_obj_tag(v_pre_1366_) == 0)
{
lean_object* v_str_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_str_1367_ = lean_ctor_get(v_x_1365_, 1);
v___x_1368_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___closed__0));
v___x_1369_ = lean_string_dec_eq(v_str_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
return v___x_1369_;
}
else
{
return v_suppressElabErrors_1363_;
}
}
else
{
return v___x_1364_;
}
}
else
{
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1370_, lean_object* v___x_1371_, lean_object* v_x_1372_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1373_; uint8_t v___x_14271__boxed_1374_; uint8_t v_res_1375_; lean_object* v_r_1376_; 
v_suppressElabErrors_boxed_1373_ = lean_unbox(v_suppressElabErrors_1370_);
v___x_14271__boxed_1374_ = lean_unbox(v___x_1371_);
v_res_1375_ = l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0(v_suppressElabErrors_boxed_1373_, v___x_14271__boxed_1374_, v_x_1372_);
lean_dec(v_x_1372_);
v_r_1376_ = lean_box(v_res_1375_);
return v_r_1376_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1377_, uint8_t v___x_1378_, lean_object* v_x_1379_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 1)
{
lean_object* v_pre_1380_; 
v_pre_1380_ = lean_ctor_get(v_x_1379_, 0);
if (lean_obj_tag(v_pre_1380_) == 0)
{
lean_object* v_str_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_str_1381_ = lean_ctor_get(v_x_1379_, 1);
v___x_1382_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___closed__0));
v___x_1383_ = lean_string_dec_eq(v_str_1381_, v___x_1382_);
if (v___x_1383_ == 0)
{
return v___x_1383_;
}
else
{
return v_suppressElabErrors_1377_;
}
}
else
{
return v___x_1378_;
}
}
else
{
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1384_, lean_object* v___x_1385_, lean_object* v_x_1386_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1387_; uint8_t v___x_14287__boxed_1388_; uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_suppressElabErrors_boxed_1387_ = lean_unbox(v_suppressElabErrors_1384_);
v___x_14287__boxed_1388_ = lean_unbox(v___x_1385_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1387_, v___x_14287__boxed_1388_, v_x_1386_);
lean_dec(v_x_1386_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(lean_object* v_ictx_1391_, lean_object* v___x_1392_, lean_object* v_as_1393_, size_t v_sz_1394_, size_t v_i_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_a_1401_; uint8_t v___x_1405_; 
v___x_1405_ = lean_usize_dec_lt(v_i_1395_, v_sz_1394_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v_ictx_1391_);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_b_1396_);
return v___x_1406_;
}
else
{
lean_object* v_a_1407_; lean_object* v_snd_1408_; lean_object* v_fst_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1497_; 
v_a_1407_ = lean_array_uget(v_as_1393_, v_i_1395_);
v_snd_1408_ = lean_ctor_get(v_a_1407_, 1);
v_fst_1409_ = lean_ctor_get(v_a_1407_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_a_1407_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1411_ = v_a_1407_;
v_isShared_1412_ = v_isSharedCheck_1497_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_snd_1408_);
lean_inc(v_fst_1409_);
lean_dec(v_a_1407_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1497_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_snd_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1495_; 
v_snd_1413_ = lean_ctor_get(v_snd_1408_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_snd_1408_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v_snd_1408_, 0);
lean_dec(v_unused_1496_);
v___x_1415_ = v_snd_1408_;
v_isShared_1416_ = v_isSharedCheck_1495_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_snd_1413_);
lean_dec(v_snd_1408_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1495_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
uint8_t v_suppressElabErrors_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___y_1421_; 
v_suppressElabErrors_1417_ = lean_ctor_get_uint8(v___y_1397_, sizeof(void*)*10);
v___x_1418_ = lean_box(0);
lean_inc_ref(v_ictx_1391_);
v___x_1419_ = l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(v_ictx_1391_, v_fst_1409_, v_snd_1413_);
if (v_suppressElabErrors_1417_ == 0)
{
v___y_1421_ = v___y_1398_;
goto v___jp_1420_;
}
else
{
lean_object* v_data_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; uint8_t v___x_1494_; 
v_data_1488_ = lean_ctor_get(v___x_1419_, 4);
lean_inc(v_data_1488_);
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_nat_dec_eq(v___x_1392_, v___x_1489_);
v___x_1491_ = lean_box(v_suppressElabErrors_1417_);
v___x_1492_ = lean_box(v___x_1490_);
v___f_1493_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1493_, 0, v___x_1491_);
lean_closure_set(v___f_1493_, 1, v___x_1492_);
v___x_1494_ = l_Lean_MessageData_hasTag(v___f_1493_, v_data_1488_);
if (v___x_1494_ == 0)
{
lean_dec_ref(v___x_1419_);
lean_del_object(v___x_1415_);
lean_del_object(v___x_1411_);
v_a_1401_ = v___x_1418_;
goto v___jp_1400_;
}
else
{
v___y_1421_ = v___y_1398_;
goto v___jp_1420_;
}
}
v___jp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Elab_Command_getScope___redArg(v___y_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v_currNamespace_1424_; lean_object* v___x_1425_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v_currNamespace_1424_ = lean_ctor_get(v_a_1423_, 2);
lean_inc(v_currNamespace_1424_);
lean_dec(v_a_1423_);
v___x_1425_ = l_Lean_Elab_Command_getScope___redArg(v___y_1421_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v_openDecls_1427_; lean_object* v_fileName_1428_; lean_object* v_pos_1429_; lean_object* v_endPos_1430_; uint8_t v_keepFullRange_1431_; uint8_t v_severity_1432_; uint8_t v_isSilent_1433_; lean_object* v_caption_1434_; lean_object* v_data_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1471_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v_openDecls_1427_ = lean_ctor_get(v_a_1426_, 3);
lean_inc(v_openDecls_1427_);
lean_dec(v_a_1426_);
v_fileName_1428_ = lean_ctor_get(v___x_1419_, 0);
v_pos_1429_ = lean_ctor_get(v___x_1419_, 1);
v_endPos_1430_ = lean_ctor_get(v___x_1419_, 2);
v_keepFullRange_1431_ = lean_ctor_get_uint8(v___x_1419_, sizeof(void*)*5);
v_severity_1432_ = lean_ctor_get_uint8(v___x_1419_, sizeof(void*)*5 + 1);
v_isSilent_1433_ = lean_ctor_get_uint8(v___x_1419_, sizeof(void*)*5 + 2);
v_caption_1434_ = lean_ctor_get(v___x_1419_, 3);
v_data_1435_ = lean_ctor_get(v___x_1419_, 4);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1437_ = v___x_1419_;
v_isShared_1438_ = v_isSharedCheck_1471_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_data_1435_);
lean_inc(v_caption_1434_);
lean_inc(v_endPos_1430_);
lean_inc(v_pos_1429_);
lean_inc(v_fileName_1428_);
lean_dec(v___x_1419_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1471_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v_openDecls_1427_);
lean_ctor_set(v___x_1415_, 0, v_currNamespace_1424_);
v___x_1440_ = v___x_1415_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_currNamespace_1424_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_openDecls_1427_);
v___x_1440_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set_tag(v___x_1411_, 4);
lean_ctor_set(v___x_1411_, 1, v_data_1435_);
lean_ctor_set(v___x_1411_, 0, v___x_1440_);
v___x_1442_ = v___x_1411_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_data_1435_);
v___x_1442_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 4, v___x_1442_);
v___x_1444_ = v___x_1437_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_fileName_1428_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_endPos_1430_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_caption_1434_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v___x_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*5, v_keepFullRange_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*5 + 1, v_severity_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*5 + 2, v_isSilent_1433_);
v___x_1444_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v_env_1446_; lean_object* v_messages_1447_; lean_object* v_scopes_1448_; lean_object* v_usedQuotCtxts_1449_; lean_object* v_nextMacroScope_1450_; lean_object* v_maxRecDepth_1451_; lean_object* v_ngen_1452_; lean_object* v_auxDeclNGen_1453_; lean_object* v_infoState_1454_; lean_object* v_traceState_1455_; lean_object* v_snapshotTasks_1456_; lean_object* v_prevLinterStates_1457_; lean_object* v_codeQualityEntryTasks_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1467_; 
v___x_1445_ = lean_st_ref_take(v___y_1421_);
v_env_1446_ = lean_ctor_get(v___x_1445_, 0);
v_messages_1447_ = lean_ctor_get(v___x_1445_, 1);
v_scopes_1448_ = lean_ctor_get(v___x_1445_, 2);
v_usedQuotCtxts_1449_ = lean_ctor_get(v___x_1445_, 3);
v_nextMacroScope_1450_ = lean_ctor_get(v___x_1445_, 4);
v_maxRecDepth_1451_ = lean_ctor_get(v___x_1445_, 5);
v_ngen_1452_ = lean_ctor_get(v___x_1445_, 6);
v_auxDeclNGen_1453_ = lean_ctor_get(v___x_1445_, 7);
v_infoState_1454_ = lean_ctor_get(v___x_1445_, 8);
v_traceState_1455_ = lean_ctor_get(v___x_1445_, 9);
v_snapshotTasks_1456_ = lean_ctor_get(v___x_1445_, 10);
v_prevLinterStates_1457_ = lean_ctor_get(v___x_1445_, 11);
v_codeQualityEntryTasks_1458_ = lean_ctor_get(v___x_1445_, 12);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1460_ = v___x_1445_;
v_isShared_1461_ = v_isSharedCheck_1467_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1458_);
lean_inc(v_prevLinterStates_1457_);
lean_inc(v_snapshotTasks_1456_);
lean_inc(v_traceState_1455_);
lean_inc(v_infoState_1454_);
lean_inc(v_auxDeclNGen_1453_);
lean_inc(v_ngen_1452_);
lean_inc(v_maxRecDepth_1451_);
lean_inc(v_nextMacroScope_1450_);
lean_inc(v_usedQuotCtxts_1449_);
lean_inc(v_scopes_1448_);
lean_inc(v_messages_1447_);
lean_inc(v_env_1446_);
lean_dec(v___x_1445_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1467_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = l_Lean_MessageLog_add(v___x_1444_, v_messages_1447_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_env_1446_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_scopes_1448_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v_usedQuotCtxts_1449_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v_nextMacroScope_1450_);
lean_ctor_set(v_reuseFailAlloc_1466_, 5, v_maxRecDepth_1451_);
lean_ctor_set(v_reuseFailAlloc_1466_, 6, v_ngen_1452_);
lean_ctor_set(v_reuseFailAlloc_1466_, 7, v_auxDeclNGen_1453_);
lean_ctor_set(v_reuseFailAlloc_1466_, 8, v_infoState_1454_);
lean_ctor_set(v_reuseFailAlloc_1466_, 9, v_traceState_1455_);
lean_ctor_set(v_reuseFailAlloc_1466_, 10, v_snapshotTasks_1456_);
lean_ctor_set(v_reuseFailAlloc_1466_, 11, v_prevLinterStates_1457_);
lean_ctor_set(v_reuseFailAlloc_1466_, 12, v_codeQualityEntryTasks_1458_);
v___x_1464_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_st_ref_put(v___y_1421_, v___x_1464_);
v_a_1401_ = v___x_1418_;
goto v___jp_1400_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_currNamespace_1424_);
lean_dec_ref(v___x_1419_);
lean_del_object(v___x_1415_);
lean_del_object(v___x_1411_);
lean_dec_ref(v_ictx_1391_);
v_a_1472_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1425_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1425_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___x_1419_);
lean_del_object(v___x_1415_);
lean_del_object(v___x_1411_);
lean_dec_ref(v_ictx_1391_);
v_a_1480_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1422_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1422_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
}
v___jp_1400_:
{
size_t v___x_1402_; size_t v___x_1403_; 
v___x_1402_ = ((size_t)1ULL);
v___x_1403_ = lean_usize_add(v_i_1395_, v___x_1402_);
v_i_1395_ = v___x_1403_;
v_b_1396_ = v_a_1401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2___boxed(lean_object* v_ictx_1498_, lean_object* v___x_1499_, lean_object* v_as_1500_, lean_object* v_sz_1501_, lean_object* v_i_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
size_t v_sz_boxed_1507_; size_t v_i_boxed_1508_; lean_object* v_res_1509_; 
v_sz_boxed_1507_ = lean_unbox_usize(v_sz_1501_);
lean_dec(v_sz_1501_);
v_i_boxed_1508_ = lean_unbox_usize(v_i_1502_);
lean_dec(v_i_1502_);
v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v_ictx_1498_, v___x_1499_, v_as_1500_, v_sz_boxed_1507_, v_i_boxed_1508_, v_b_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v_as_1500_);
lean_dec(v___x_1499_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(lean_object* v_docComment_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v_fileMap_1576_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v_____x_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___x_1687_; 
v_fileMap_1576_ = lean_ctor_get(v___y_1513_, 1);
v___x_1687_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_1512_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v_a_1688_, v___y_1513_, v___y_1514_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1698_; 
v_a_1698_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1687_, 1);
v_____x_1677_ = v_a_1698_;
v___y_1678_ = v___y_1513_;
v___y_1679_ = v___y_1514_;
goto v___jp_1676_;
}
v___jp_1516_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
v___jp_1519_:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Elab_Command_getScope___redArg(v___y_1527_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v_currNamespace_1530_; lean_object* v___x_1531_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v_currNamespace_1530_ = lean_ctor_get(v_a_1529_, 2);
lean_inc(v_currNamespace_1530_);
lean_dec(v_a_1529_);
v___x_1531_ = l_Lean_Elab_Command_getScope___redArg(v___y_1527_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_openDecls_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_env_1538_; lean_object* v_messages_1539_; lean_object* v_scopes_1540_; lean_object* v_usedQuotCtxts_1541_; lean_object* v_nextMacroScope_1542_; lean_object* v_maxRecDepth_1543_; lean_object* v_ngen_1544_; lean_object* v_auxDeclNGen_1545_; lean_object* v_infoState_1546_; lean_object* v_traceState_1547_; lean_object* v_snapshotTasks_1548_; lean_object* v_prevLinterStates_1549_; lean_object* v_codeQualityEntryTasks_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1559_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v_openDecls_1533_ = lean_ctor_get(v_a_1532_, 3);
lean_inc(v_openDecls_1533_);
lean_dec(v_a_1532_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v_currNamespace_1530_);
lean_ctor_set(v___x_1534_, 1, v_openDecls_1533_);
v___x_1535_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___y_1526_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1523_);
v___x_1536_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1536_, 0, v___y_1523_);
lean_ctor_set(v___x_1536_, 1, v___y_1521_);
lean_ctor_set(v___x_1536_, 2, v___y_1522_);
lean_ctor_set(v___x_1536_, 3, v___y_1525_);
lean_ctor_set(v___x_1536_, 4, v___x_1535_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*5, v___y_1524_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*5 + 1, v___y_1520_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*5 + 2, v___y_1524_);
v___x_1537_ = lean_st_ref_take(v___y_1527_);
v_env_1538_ = lean_ctor_get(v___x_1537_, 0);
v_messages_1539_ = lean_ctor_get(v___x_1537_, 1);
v_scopes_1540_ = lean_ctor_get(v___x_1537_, 2);
v_usedQuotCtxts_1541_ = lean_ctor_get(v___x_1537_, 3);
v_nextMacroScope_1542_ = lean_ctor_get(v___x_1537_, 4);
v_maxRecDepth_1543_ = lean_ctor_get(v___x_1537_, 5);
v_ngen_1544_ = lean_ctor_get(v___x_1537_, 6);
v_auxDeclNGen_1545_ = lean_ctor_get(v___x_1537_, 7);
v_infoState_1546_ = lean_ctor_get(v___x_1537_, 8);
v_traceState_1547_ = lean_ctor_get(v___x_1537_, 9);
v_snapshotTasks_1548_ = lean_ctor_get(v___x_1537_, 10);
v_prevLinterStates_1549_ = lean_ctor_get(v___x_1537_, 11);
v_codeQualityEntryTasks_1550_ = lean_ctor_get(v___x_1537_, 12);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1552_ = v___x_1537_;
v_isShared_1553_ = v_isSharedCheck_1559_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1550_);
lean_inc(v_prevLinterStates_1549_);
lean_inc(v_snapshotTasks_1548_);
lean_inc(v_traceState_1547_);
lean_inc(v_infoState_1546_);
lean_inc(v_auxDeclNGen_1545_);
lean_inc(v_ngen_1544_);
lean_inc(v_maxRecDepth_1543_);
lean_inc(v_nextMacroScope_1542_);
lean_inc(v_usedQuotCtxts_1541_);
lean_inc(v_scopes_1540_);
lean_inc(v_messages_1539_);
lean_inc(v_env_1538_);
lean_dec(v___x_1537_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1559_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1554_ = l_Lean_MessageLog_add(v___x_1536_, v_messages_1539_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v___x_1554_);
v___x_1556_ = v___x_1552_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_env_1538_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_scopes_1540_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_usedQuotCtxts_1541_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_nextMacroScope_1542_);
lean_ctor_set(v_reuseFailAlloc_1558_, 5, v_maxRecDepth_1543_);
lean_ctor_set(v_reuseFailAlloc_1558_, 6, v_ngen_1544_);
lean_ctor_set(v_reuseFailAlloc_1558_, 7, v_auxDeclNGen_1545_);
lean_ctor_set(v_reuseFailAlloc_1558_, 8, v_infoState_1546_);
lean_ctor_set(v_reuseFailAlloc_1558_, 9, v_traceState_1547_);
lean_ctor_set(v_reuseFailAlloc_1558_, 10, v_snapshotTasks_1548_);
lean_ctor_set(v_reuseFailAlloc_1558_, 11, v_prevLinterStates_1549_);
lean_ctor_set(v_reuseFailAlloc_1558_, 12, v_codeQualityEntryTasks_1550_);
v___x_1556_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_st_ref_put(v___y_1527_, v___x_1556_);
goto v___jp_1516_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_currNamespace_1530_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v___y_1521_);
v_a_1560_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1531_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1531_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v___y_1521_);
v_a_1568_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1528_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1528_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
v___jp_1577_:
{
lean_object* v___x_1584_; lean_object* v_env_1585_; lean_object* v_fileName_1586_; uint8_t v_suppressElabErrors_1587_; lean_object* v_ictx_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_scopes_1591_; lean_object* v___x_1592_; lean_object* v_opts_1593_; lean_object* v___x_1594_; 
v___x_1584_ = lean_st_ref_get(v___y_1581_);
v_env_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_ref(v_env_1585_);
lean_dec(v___x_1584_);
v_fileName_1586_ = lean_ctor_get(v___y_1579_, 0);
v_suppressElabErrors_1587_ = lean_ctor_get_uint8(v___y_1579_, sizeof(void*)*10);
lean_inc(v___y_1583_);
lean_inc_ref(v_fileMap_1576_);
lean_inc_ref(v_fileName_1586_);
lean_inc_ref(v___y_1580_);
v_ictx_1588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_1588_, 0, v___y_1580_);
lean_ctor_set(v_ictx_1588_, 1, v_fileName_1586_);
lean_ctor_set(v_ictx_1588_, 2, v_fileMap_1576_);
lean_ctor_set(v_ictx_1588_, 3, v___y_1583_);
v___x_1589_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1590_ = lean_st_ref_get(v___y_1581_);
v_scopes_1591_ = lean_ctor_get(v___x_1590_, 2);
lean_inc(v_scopes_1591_);
lean_dec(v___x_1590_);
v___x_1592_ = l_List_head_x21___redArg(v___x_1589_, v_scopes_1591_);
lean_dec(v_scopes_1591_);
v_opts_1593_ = lean_ctor_get(v___x_1592_, 1);
lean_inc_ref(v_opts_1593_);
lean_dec(v___x_1592_);
v___x_1594_ = l_Lean_Elab_Command_getScope___redArg(v___y_1581_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v_currNamespace_1596_; lean_object* v___x_1597_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v_currNamespace_1596_ = lean_ctor_get(v_a_1595_, 2);
lean_inc(v_currNamespace_1596_);
lean_dec(v_a_1595_);
v___x_1597_ = l_Lean_Elab_Command_getScope___redArg(v___y_1581_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1659_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1659_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1659_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_openDecls_1602_; lean_object* v_pmctx_1603_; lean_object* v_blockCtxt_1604_; lean_object* v___x_1605_; lean_object* v_s_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_s_1609_; lean_object* v_errors_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_openDecls_1602_ = lean_ctor_get(v_a_1598_, 3);
lean_inc(v_openDecls_1602_);
lean_dec(v_a_1598_);
lean_inc_ref(v_env_1585_);
v_pmctx_1603_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_1603_, 0, v_env_1585_);
lean_ctor_set(v_pmctx_1603_, 1, v_opts_1593_);
lean_ctor_set(v_pmctx_1603_, 2, v_currNamespace_1596_);
lean_ctor_set(v_pmctx_1603_, 3, v_openDecls_1602_);
lean_inc(v___y_1582_);
lean_inc_ref(v_fileMap_1576_);
v_blockCtxt_1604_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_fileMap_1576_, v___y_1578_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1578_);
v___x_1605_ = l_Lean_Parser_mkParserState(v___y_1580_);
v_s_1606_ = l_Lean_Parser_ParserState_setPos(v___x_1605_, v___y_1582_);
lean_inc_ref(v_blockCtxt_1604_);
v___x_1607_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_1607_, 0, v_blockCtxt_1604_);
v___x_1608_ = l_Lean_Parser_getTokenTable(v_env_1585_);
lean_inc_ref(v___x_1608_);
lean_inc_ref(v_pmctx_1603_);
lean_inc_ref_n(v_ictx_1588_, 2);
v_s_1609_ = l_Lean_Parser_ParserFn_run(v___x_1607_, v_ictx_1588_, v_pmctx_1603_, v___x_1608_, v_s_1606_);
lean_inc_ref(v_s_1609_);
v_errors_1610_ = l___private_Lean_DocString_Add_0__Lean_parseErrors(v_ictx_1588_, v_pmctx_1603_, v___x_1608_, v___y_1580_, v_blockCtxt_1604_, v_s_1609_);
v___x_1611_ = lean_array_get_size(v_errors_1610_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_nat_dec_eq(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; size_t v_sz_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_s_1609_);
lean_del_object(v___x_1600_);
lean_dec_ref(v___y_1580_);
v___x_1614_ = lean_box(0);
v_sz_1615_ = lean_array_size(v_errors_1610_);
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__2(v_ictx_1588_, v___x_1611_, v_errors_1610_, v_sz_1615_, v___x_1616_, v___x_1614_, v___y_1579_, v___y_1581_);
lean_dec_ref(v_errors_1610_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1625_; 
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v___x_1617_, 0);
lean_dec(v_unused_1626_);
v___x_1619_ = v___x_1617_;
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v___x_1617_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_box(0);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_a_1627_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1617_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1617_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
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
else
{
lean_object* v_stxStack_1635_; lean_object* v_pos_1636_; uint8_t v___x_1637_; 
lean_dec_ref(v_errors_1610_);
v_stxStack_1635_ = lean_ctor_get(v_s_1609_, 0);
lean_inc_ref(v_stxStack_1635_);
v_pos_1636_ = lean_ctor_get(v_s_1609_, 2);
lean_inc(v_pos_1636_);
lean_dec_ref(v_s_1609_);
v___x_1637_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1588_, v_pos_1636_);
lean_dec_ref_known(v_ictx_1588_, 4);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint32_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec_ref(v_stxStack_1635_);
lean_del_object(v___x_1600_);
lean_inc_ref(v_fileMap_1576_);
v___x_1638_ = l_Lean_FileMap_toPosition(v_fileMap_1576_, v_pos_1636_);
v___x_1639_ = lean_box(0);
v___x_1640_ = 2;
v___x_1641_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7));
v___x_1642_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___closed__0));
v___x_1643_ = lean_string_utf8_get(v___y_1580_, v_pos_1636_);
lean_dec(v_pos_1636_);
lean_dec_ref(v___y_1580_);
v___x_1644_ = lean_string_push(v___x_1641_, v___x_1643_);
v___x_1645_ = lean_string_append(v___x_1642_, v___x_1644_);
lean_dec_ref(v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___closed__1));
v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
v___x_1649_ = l_Lean_MessageData_ofFormat(v___x_1648_);
if (v_suppressElabErrors_1587_ == 0)
{
v___y_1520_ = v___x_1640_;
v___y_1521_ = v___x_1638_;
v___y_1522_ = v___x_1639_;
v___y_1523_ = v_fileName_1586_;
v___y_1524_ = v___x_1637_;
v___y_1525_ = v___x_1641_;
v___y_1526_ = v___x_1649_;
v___y_1527_ = v___y_1581_;
goto v___jp_1519_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___f_1652_; uint8_t v___x_1653_; 
v___x_1650_ = lean_box(v_suppressElabErrors_1587_);
v___x_1651_ = lean_box(v___x_1637_);
v___f_1652_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1652_, 0, v___x_1650_);
lean_closure_set(v___f_1652_, 1, v___x_1651_);
lean_inc_ref(v___x_1649_);
v___x_1653_ = l_Lean_MessageData_hasTag(v___f_1652_, v___x_1649_);
if (v___x_1653_ == 0)
{
lean_dec_ref(v___x_1649_);
lean_dec_ref(v___x_1638_);
goto v___jp_1516_;
}
else
{
v___y_1520_ = v___x_1640_;
v___y_1521_ = v___x_1638_;
v___y_1522_ = v___x_1639_;
v___y_1523_ = v_fileName_1586_;
v___y_1524_ = v___x_1637_;
v___y_1525_ = v___x_1641_;
v___y_1526_ = v___x_1649_;
v___y_1527_ = v___y_1581_;
goto v___jp_1519_;
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_dec(v_pos_1636_);
lean_dec_ref(v___y_1580_);
v___x_1654_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1635_);
lean_dec_ref(v_stxStack_1635_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1655_);
v___x_1657_ = v___x_1600_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_currNamespace_1596_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref_known(v_ictx_1588_, 4);
lean_dec_ref(v_env_1585_);
lean_dec(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1578_);
v_a_1660_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1597_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1597_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec_ref(v_opts_1593_);
lean_dec_ref_known(v_ictx_1588_, 4);
lean_dec_ref(v_env_1585_);
lean_dec(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1578_);
v_a_1668_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1594_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1594_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
v___jp_1676_:
{
lean_object* v_snd_1680_; lean_object* v_fst_1681_; lean_object* v_fst_1682_; lean_object* v_snd_1683_; lean_object* v_source_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v_snd_1680_ = lean_ctor_get(v_____x_1677_, 1);
lean_inc(v_snd_1680_);
v_fst_1681_ = lean_ctor_get(v_____x_1677_, 0);
lean_inc(v_fst_1681_);
lean_dec_ref(v_____x_1677_);
v_fst_1682_ = lean_ctor_get(v_snd_1680_, 0);
lean_inc(v_fst_1682_);
v_snd_1683_ = lean_ctor_get(v_snd_1680_, 1);
lean_inc(v_snd_1683_);
lean_dec(v_snd_1680_);
v_source_1684_ = lean_ctor_get(v_fileMap_1576_, 0);
v___x_1685_ = lean_string_utf8_byte_size(v_source_1684_);
v___x_1686_ = lean_nat_dec_le(v_snd_1683_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_dec(v_snd_1683_);
lean_inc_ref(v_source_1684_);
v___y_1578_ = v_fst_1681_;
v___y_1579_ = v___y_1678_;
v___y_1580_ = v_source_1684_;
v___y_1581_ = v___y_1679_;
v___y_1582_ = v_fst_1682_;
v___y_1583_ = v___x_1685_;
goto v___jp_1577_;
}
else
{
lean_inc_ref(v_source_1684_);
v___y_1578_ = v_fst_1681_;
v___y_1579_ = v___y_1678_;
v___y_1580_ = v_source_1684_;
v___y_1581_ = v___y_1679_;
v___y_1582_ = v_fst_1682_;
v___y_1583_ = v_snd_1683_;
goto v___jp_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___boxed(lean_object* v_docComment_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(v_docComment_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v_docComment_1699_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(lean_object* v_ref_1704_, lean_object* v_msg_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Elab_Command_getRef___redArg(v___y_1706_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v_fileName_1711_; lean_object* v_fileMap_1712_; lean_object* v_currRecDepth_1713_; lean_object* v_cmdPos_1714_; lean_object* v_macroStack_1715_; lean_object* v_quotContext_x3f_1716_; lean_object* v_currMacroScope_1717_; lean_object* v_snap_x3f_1718_; lean_object* v_cancelTk_x3f_1719_; uint8_t v_suppressElabErrors_1720_; lean_object* v_ref_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v_fileName_1711_ = lean_ctor_get(v___y_1706_, 0);
v_fileMap_1712_ = lean_ctor_get(v___y_1706_, 1);
v_currRecDepth_1713_ = lean_ctor_get(v___y_1706_, 2);
v_cmdPos_1714_ = lean_ctor_get(v___y_1706_, 3);
v_macroStack_1715_ = lean_ctor_get(v___y_1706_, 4);
v_quotContext_x3f_1716_ = lean_ctor_get(v___y_1706_, 5);
v_currMacroScope_1717_ = lean_ctor_get(v___y_1706_, 6);
v_snap_x3f_1718_ = lean_ctor_get(v___y_1706_, 8);
v_cancelTk_x3f_1719_ = lean_ctor_get(v___y_1706_, 9);
v_suppressElabErrors_1720_ = lean_ctor_get_uint8(v___y_1706_, sizeof(void*)*10);
v_ref_1721_ = l_Lean_replaceRef(v_ref_1704_, v_a_1710_);
lean_dec(v_a_1710_);
lean_inc(v_cancelTk_x3f_1719_);
lean_inc(v_snap_x3f_1718_);
lean_inc(v_currMacroScope_1717_);
lean_inc(v_quotContext_x3f_1716_);
lean_inc(v_macroStack_1715_);
lean_inc(v_cmdPos_1714_);
lean_inc(v_currRecDepth_1713_);
lean_inc_ref(v_fileMap_1712_);
lean_inc_ref(v_fileName_1711_);
v___x_1722_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1722_, 0, v_fileName_1711_);
lean_ctor_set(v___x_1722_, 1, v_fileMap_1712_);
lean_ctor_set(v___x_1722_, 2, v_currRecDepth_1713_);
lean_ctor_set(v___x_1722_, 3, v_cmdPos_1714_);
lean_ctor_set(v___x_1722_, 4, v_macroStack_1715_);
lean_ctor_set(v___x_1722_, 5, v_quotContext_x3f_1716_);
lean_ctor_set(v___x_1722_, 6, v_currMacroScope_1717_);
lean_ctor_set(v___x_1722_, 7, v_ref_1721_);
lean_ctor_set(v___x_1722_, 8, v_snap_x3f_1718_);
lean_ctor_set(v___x_1722_, 9, v_cancelTk_x3f_1719_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*10, v_suppressElabErrors_1720_);
v___x_1723_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v_msg_1705_, v___x_1722_, v___y_1707_);
lean_dec_ref_known(v___x_1722_, 10);
return v___x_1723_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v_msg_1705_);
v_a_1724_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1709_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1709_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg___boxed(lean_object* v_ref_1732_, lean_object* v_msg_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1732_, v_msg_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_ref_1732_);
return v_res_1737_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__0));
v___x_1740_ = l_Lean_stringToMessageData(v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(lean_object* v_stx_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_unsigned_to_nat(1u);
v___x_1756_ = l_Lean_Syntax_getArg(v_stx_1745_, v___x_1755_);
if (lean_obj_tag(v___x_1756_) == 1)
{
lean_object* v_kind_1757_; 
v_kind_1757_ = lean_ctor_get(v___x_1756_, 1);
lean_inc(v_kind_1757_);
if (lean_obj_tag(v_kind_1757_) == 1)
{
lean_object* v_pre_1758_; 
v_pre_1758_ = lean_ctor_get(v_kind_1757_, 0);
lean_inc(v_pre_1758_);
if (lean_obj_tag(v_pre_1758_) == 1)
{
lean_object* v_pre_1759_; 
v_pre_1759_ = lean_ctor_get(v_pre_1758_, 0);
lean_inc(v_pre_1759_);
if (lean_obj_tag(v_pre_1759_) == 1)
{
lean_object* v_pre_1760_; 
v_pre_1760_ = lean_ctor_get(v_pre_1759_, 0);
lean_inc(v_pre_1760_);
if (lean_obj_tag(v_pre_1760_) == 1)
{
lean_object* v_pre_1761_; 
v_pre_1761_ = lean_ctor_get(v_pre_1760_, 0);
if (lean_obj_tag(v_pre_1761_) == 0)
{
lean_object* v_args_1762_; lean_object* v_str_1763_; lean_object* v_str_1764_; lean_object* v_str_1765_; lean_object* v_str_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_args_1762_ = lean_ctor_get(v___x_1756_, 2);
lean_inc_ref(v_args_1762_);
lean_dec_ref_known(v___x_1756_, 3);
v_str_1763_ = lean_ctor_get(v_kind_1757_, 1);
lean_inc_ref(v_str_1763_);
lean_dec_ref_known(v_kind_1757_, 2);
v_str_1764_ = lean_ctor_get(v_pre_1758_, 1);
lean_inc_ref(v_str_1764_);
lean_dec_ref_known(v_pre_1758_, 2);
v_str_1765_ = lean_ctor_get(v_pre_1759_, 1);
lean_inc_ref(v_str_1765_);
lean_dec_ref_known(v_pre_1759_, 2);
v_str_1766_ = lean_ctor_get(v_pre_1760_, 1);
lean_inc_ref(v_str_1766_);
lean_dec_ref_known(v_pre_1760_, 2);
v___x_1767_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__2));
v___x_1768_ = lean_string_dec_eq(v_str_1766_, v___x_1767_);
lean_dec_ref(v_str_1766_);
if (v___x_1768_ == 0)
{
lean_dec_ref(v_str_1765_);
lean_dec_ref(v_str_1764_);
lean_dec_ref(v_str_1763_);
lean_dec_ref(v_args_1762_);
goto v___jp_1749_;
}
else
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__3));
v___x_1770_ = lean_string_dec_eq(v_str_1765_, v___x_1769_);
lean_dec_ref(v_str_1765_);
if (v___x_1770_ == 0)
{
lean_dec_ref(v_str_1764_);
lean_dec_ref(v_str_1763_);
lean_dec_ref(v_args_1762_);
goto v___jp_1749_;
}
else
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__4));
v___x_1772_ = lean_string_dec_eq(v_str_1764_, v___x_1771_);
lean_dec_ref(v_str_1764_);
if (v___x_1772_ == 0)
{
lean_dec_ref(v_str_1763_);
lean_dec_ref(v_args_1762_);
goto v___jp_1749_;
}
else
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__5));
v___x_1774_ = lean_string_dec_eq(v_str_1763_, v___x_1773_);
lean_dec_ref(v_str_1763_);
if (v___x_1774_ == 0)
{
lean_dec_ref(v_args_1762_);
goto v___jp_1749_;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_array_get_size(v_args_1762_);
v___x_1776_ = lean_unsigned_to_nat(2u);
v___x_1777_ = lean_nat_dec_eq(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v_args_1762_);
goto v___jp_1749_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_array_fget(v_args_1762_, v___x_1778_);
lean_dec_ref(v_args_1762_);
if (lean_obj_tag(v___x_1779_) == 2)
{
lean_object* v_val_1780_; lean_object* v___x_1781_; 
lean_dec(v_stx_1745_);
v_val_1780_ = lean_ctor_get(v___x_1779_, 1);
lean_inc_ref(v_val_1780_);
lean_dec_ref_known(v___x_1779_, 2);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_val_1780_);
return v___x_1781_;
}
else
{
lean_dec(v___x_1779_);
goto v___jp_1749_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1760_, 2);
lean_dec_ref_known(v_pre_1759_, 2);
lean_dec_ref_known(v_pre_1758_, 2);
lean_dec_ref_known(v_kind_1757_, 2);
lean_dec_ref_known(v___x_1756_, 3);
goto v___jp_1749_;
}
}
else
{
lean_dec_ref_known(v_pre_1759_, 2);
lean_dec(v_pre_1760_);
lean_dec_ref_known(v_pre_1758_, 2);
lean_dec_ref_known(v_kind_1757_, 2);
lean_dec_ref_known(v___x_1756_, 3);
goto v___jp_1749_;
}
}
else
{
lean_dec(v_pre_1759_);
lean_dec_ref_known(v_pre_1758_, 2);
lean_dec_ref_known(v_kind_1757_, 2);
lean_dec_ref_known(v___x_1756_, 3);
goto v___jp_1749_;
}
}
else
{
lean_dec_ref_known(v_kind_1757_, 2);
lean_dec(v_pre_1758_);
lean_dec_ref_known(v___x_1756_, 3);
goto v___jp_1749_;
}
}
else
{
lean_dec_ref_known(v___x_1756_, 3);
lean_dec(v_kind_1757_);
goto v___jp_1749_;
}
}
else
{
lean_dec(v___x_1756_);
goto v___jp_1749_;
}
v___jp_1749_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1750_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___closed__1);
lean_inc(v_stx_1745_);
v___x_1751_ = l_Lean_MessageData_ofSyntax(v_stx_1745_);
v___x_1752_ = l_Lean_indentD(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1750_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_stx_1745_, v___x_1753_, v___y_1746_, v___y_1747_);
lean_dec(v_stx_1745_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0___boxed(lean_object* v_stx_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_stx_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(lean_object* v_doc_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
uint8_t v___x_1791_; 
v___x_1791_ = l_Lean_isVersoDocComment(v_doc_1787_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0(v_doc_1787_, v_a_1788_, v_a_1789_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1(v_doc_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_doc_1787_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1824_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1824_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1824_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
if (lean_obj_tag(v_a_1794_) == 1)
{
lean_object* v_val_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_del_object(v___x_1796_);
v_val_1798_ = lean_ctor_get(v_a_1794_, 0);
lean_inc(v_val_1798_);
lean_dec_ref_known(v_a_1794_, 1);
v___x_1799_ = l_Lean_TSyntax_getVersoBlocks(v_val_1798_);
lean_dec(v_val_1798_);
v___x_1800_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1800_, 0, v___x_1799_);
v___x_1801_ = 0;
v___x_1802_ = lean_box(v___x_1801_);
v___x_1803_ = lean_alloc_closure((void*)(l_Lean_Doc_DocM_execForModule___boxed), 10, 3);
lean_closure_set(v___x_1803_, 0, lean_box(0));
lean_closure_set(v___x_1803_, 1, v___x_1800_);
lean_closure_set(v___x_1803_, 2, v___x_1802_);
v___x_1804_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_1803_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v_fst_1806_; lean_object* v_fst_1807_; lean_object* v_snd_1808_; lean_object* v___f_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v_fst_1806_ = lean_ctor_get(v_a_1805_, 0);
lean_inc(v_fst_1806_);
lean_dec(v_a_1805_);
v_fst_1807_ = lean_ctor_get(v_fst_1806_, 0);
lean_inc(v_fst_1807_);
v_snd_1808_ = lean_ctor_get(v_fst_1806_, 1);
lean_inc(v_snd_1808_);
lean_dec(v_fst_1806_);
v___f_1809_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1809_, 0, v_fst_1807_);
lean_closure_set(v___f_1809_, 1, v_snd_1808_);
v___x_1810_ = lean_alloc_closure((void*)(l_Lean_Doc_MarkdownM_run_x27___boxed), 4, 1);
lean_closure_set(v___x_1810_, 0, v___f_1809_);
v___x_1811_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1810_, v_a_1788_, v_a_1789_);
return v___x_1811_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1804_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1804_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_dec(v_a_1794_);
v___x_1820_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7));
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1820_);
v___x_1822_ = v___x_1796_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
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
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1793_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1793_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown___boxed(lean_object* v_doc_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_doc_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(lean_object* v_p_1838_, lean_object* v_level_1839_, lean_object* v_part_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___redArg(v_level_1839_, v_part_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2___boxed(lean_object* v_p_1846_, lean_object* v_level_1847_, lean_object* v_part_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2(v_p_1846_, v_level_1847_, v_part_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec(v_level_1847_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(lean_object* v_00_u03b1_1854_, lean_object* v_ref_1855_, lean_object* v_msg_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_ref_1855_, v_msg_1856_, v___y_1857_, v___y_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_ref_1862_, lean_object* v_msg_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0(v_00_u03b1_1861_, v_ref_1862_, v_msg_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v_ref_1862_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4(lean_object* v_msgData_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg(v_msgData_1868_, v___y_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___boxed(lean_object* v_msgData_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4(v_msgData_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(lean_object* v_00_u03b1_1878_, lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v_msg_1879_, v___y_1880_, v___y_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1884_, lean_object* v_msg_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3(v_00_u03b1_1884_, v_msg_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(lean_object* v_p_1890_, lean_object* v___x_1891_, size_t v_sz_1892_, size_t v_i_1893_, lean_object* v_bs_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___redArg(v___x_1891_, v_sz_1892_, v_i_1893_, v_bs_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8___boxed(lean_object* v_p_1900_, lean_object* v___x_1901_, lean_object* v_sz_1902_, lean_object* v_i_1903_, lean_object* v_bs_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
size_t v_sz_boxed_1909_; size_t v_i_boxed_1910_; lean_object* v_res_1911_; 
v_sz_boxed_1909_ = lean_unbox_usize(v_sz_1902_);
lean_dec(v_sz_1902_);
v_i_boxed_1910_ = lean_unbox_usize(v_i_1903_);
lean_dec(v_i_1903_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__8(v_p_1900_, v___x_1901_, v_sz_boxed_1909_, v_i_boxed_1910_, v_bs_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec(v___x_1901_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5(lean_object* v_msgData_1912_, lean_object* v_macroStack_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___redArg(v_msgData_1912_, v_macroStack_1913_, v___y_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5___boxed(lean_object* v_msgData_1918_, lean_object* v_macroStack_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5(v_msgData_1918_, v_macroStack_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1924_, lean_object* v___x_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1924_, v___x_1925_, v___y_1930_, v___y_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object* v___x_1934_, lean_object* v___x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(v___x_1934_, v___x_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1943_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_1952_ = l_Lean_stringToMessageData(v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_1955_ = l_Lean_stringToMessageData(v___x_1954_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6));
v___x_1958_ = l_Lean_stringToMessageData(v___x_1957_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
v___x_1961_ = l_Lean_stringToMessageData(v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14));
v___x_1973_ = l_Lean_stringToMessageData(v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
lean_inc(v_x_1974_);
v___x_1979_ = l_Lean_Syntax_isOfKind(v_x_1974_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v_x_1974_);
v___x_1980_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1981_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_1980_, v_a_1975_, v_a_1976_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = l_Lean_Syntax_getArg(v_x_1974_, v___x_1982_);
lean_inc(v___x_1983_);
v___x_1984_ = l_Lean_Syntax_matchesNull(v___x_1983_, v___x_1982_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1983_);
v___x_1986_ = l_Lean_Syntax_matchesNull(v___x_1983_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec(v___x_1983_);
lean_dec(v_x_1974_);
v___x_1987_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_1988_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_1987_, v_a_1975_, v_a_1976_);
return v___x_1988_;
}
else
{
lean_object* v_docs_1989_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; uint8_t v___y_2045_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2061_; 
v_docs_1989_ = l_Lean_Syntax_getArg(v___x_1983_, v___x_1982_);
lean_dec(v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_docs_1989_);
v___x_2095_ = l_Lean_Syntax_isOfKind(v_docs_1989_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v_docs_1989_);
lean_dec(v_x_1974_);
v___x_2096_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_2097_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_2096_, v_a_1975_, v_a_1976_);
return v___x_2097_;
}
else
{
goto v___jp_2087_;
}
}
else
{
goto v___jp_2087_;
}
v___jp_1990_:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_docs_1989_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2031_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2031_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2031_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v_env_2000_; lean_object* v_messages_2001_; lean_object* v_scopes_2002_; lean_object* v_usedQuotCtxts_2003_; lean_object* v_nextMacroScope_2004_; lean_object* v_maxRecDepth_2005_; lean_object* v_ngen_2006_; lean_object* v_auxDeclNGen_2007_; lean_object* v_infoState_2008_; lean_object* v_traceState_2009_; lean_object* v_snapshotTasks_2010_; lean_object* v_prevLinterStates_2011_; lean_object* v_codeQualityEntryTasks_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2030_; 
v___x_1999_ = lean_st_ref_take(v___y_1993_);
v_env_2000_ = lean_ctor_get(v___x_1999_, 0);
v_messages_2001_ = lean_ctor_get(v___x_1999_, 1);
v_scopes_2002_ = lean_ctor_get(v___x_1999_, 2);
v_usedQuotCtxts_2003_ = lean_ctor_get(v___x_1999_, 3);
v_nextMacroScope_2004_ = lean_ctor_get(v___x_1999_, 4);
v_maxRecDepth_2005_ = lean_ctor_get(v___x_1999_, 5);
v_ngen_2006_ = lean_ctor_get(v___x_1999_, 6);
v_auxDeclNGen_2007_ = lean_ctor_get(v___x_1999_, 7);
v_infoState_2008_ = lean_ctor_get(v___x_1999_, 8);
v_traceState_2009_ = lean_ctor_get(v___x_1999_, 9);
v_snapshotTasks_2010_ = lean_ctor_get(v___x_1999_, 10);
v_prevLinterStates_2011_ = lean_ctor_get(v___x_1999_, 11);
v_codeQualityEntryTasks_2012_ = lean_ctor_get(v___x_1999_, 12);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2014_ = v___x_1999_;
v_isShared_2015_ = v_isSharedCheck_2030_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2012_);
lean_inc(v_prevLinterStates_2011_);
lean_inc(v_snapshotTasks_2010_);
lean_inc(v_traceState_2009_);
lean_inc(v_infoState_2008_);
lean_inc(v_auxDeclNGen_2007_);
lean_inc(v_ngen_2006_);
lean_inc(v_maxRecDepth_2005_);
lean_inc(v_nextMacroScope_2004_);
lean_inc(v_usedQuotCtxts_2003_);
lean_inc(v_scopes_2002_);
lean_inc(v_messages_2001_);
lean_inc(v_env_2000_);
lean_dec(v___x_1999_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2030_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v_toEnvExtension_2017_; lean_object* v_asyncMode_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2016_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_2017_ = lean_ctor_get(v___x_2016_, 0);
v_asyncMode_2018_ = lean_ctor_get(v_toEnvExtension_2017_, 2);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___y_1991_);
lean_ctor_set(v___x_2019_, 1, v_a_1995_);
v___x_2020_ = lean_box(0);
v___x_2021_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2016_, v_env_2000_, v___x_2019_, v_asyncMode_2018_, v___x_2020_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2021_);
v___x_2023_ = v___x_2014_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_messages_2001_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_scopes_2002_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_usedQuotCtxts_2003_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_nextMacroScope_2004_);
lean_ctor_set(v_reuseFailAlloc_2029_, 5, v_maxRecDepth_2005_);
lean_ctor_set(v_reuseFailAlloc_2029_, 6, v_ngen_2006_);
lean_ctor_set(v_reuseFailAlloc_2029_, 7, v_auxDeclNGen_2007_);
lean_ctor_set(v_reuseFailAlloc_2029_, 8, v_infoState_2008_);
lean_ctor_set(v_reuseFailAlloc_2029_, 9, v_traceState_2009_);
lean_ctor_set(v_reuseFailAlloc_2029_, 10, v_snapshotTasks_2010_);
lean_ctor_set(v_reuseFailAlloc_2029_, 11, v_prevLinterStates_2011_);
lean_ctor_set(v_reuseFailAlloc_2029_, 12, v_codeQualityEntryTasks_2012_);
v___x_2023_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2024_ = lean_st_ref_put(v___y_1993_, v___x_2023_);
v___x_2025_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2025_);
v___x_2027_ = v___x_1997_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v___y_1991_);
v_a_2032_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1994_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1994_);
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
v___jp_2040_:
{
if (v___y_2045_ == 0)
{
lean_dec(v___y_2041_);
v___y_1991_ = v___y_2042_;
v___y_1992_ = v___y_2044_;
v___y_1993_ = v___y_2043_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec(v_docs_1989_);
v___x_2046_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_2047_ = l_Lean_MessageData_ofConstName(v___y_2042_, v___x_1984_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_2041_, v___x_2050_, v___y_2044_, v___y_2043_);
lean_dec(v___y_2041_);
return v___x_2051_;
}
}
v___jp_2052_:
{
lean_object* v___x_2057_; lean_object* v_env_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_st_ref_get(v___y_2056_);
v_env_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc_ref(v_env_2058_);
lean_dec(v___x_2057_);
v___x_2059_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_2058_, v___y_2054_);
if (v___x_2059_ == 0)
{
v___y_2041_ = v___y_2053_;
v___y_2042_ = v___y_2054_;
v___y_2043_ = v___y_2056_;
v___y_2044_ = v___y_2055_;
v___y_2045_ = v___x_1986_;
goto v___jp_2040_;
}
else
{
v___y_2041_ = v___y_2053_;
v___y_2042_ = v___y_2054_;
v___y_2043_ = v___y_2056_;
v___y_2044_ = v___y_2055_;
v___y_2045_ = v___x_1984_;
goto v___jp_2040_;
}
}
v___jp_2060_:
{
lean_object* v___x_2062_; lean_object* v___f_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_box(0);
lean_inc(v___y_2061_);
v___f_2063_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2063_, 0, v___y_2061_);
lean_closure_set(v___f_2063_, 1, v___x_2062_);
v___x_2064_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2063_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; lean_object* v_env_2067_; lean_object* v___x_2068_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc_n(v_a_2065_, 2);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = lean_st_ref_get(v_a_1976_);
v_env_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_env_2067_);
lean_dec(v___x_2066_);
v___x_2068_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_2067_, v_a_2065_);
if (lean_obj_tag(v___x_2068_) == 1)
{
lean_object* v_val_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v_docs_1989_);
v_val_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v___x_2070_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_2071_ = l_Lean_MessageData_ofConstName(v_a_2065_, v___x_1984_);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_MessageData_ofConstName(v_val_2069_, v___x_1984_);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___x_2070_);
v___x_2078_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v___y_2061_, v___x_2077_, v_a_1975_, v_a_1976_);
lean_dec(v___y_2061_);
return v___x_2078_;
}
else
{
lean_dec(v___x_2068_);
v___y_2053_ = v___y_2061_;
v___y_2054_ = v_a_2065_;
v___y_2055_ = v_a_1975_;
v___y_2056_ = v_a_1976_;
goto v___jp_2052_;
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v___y_2061_);
lean_dec(v_docs_1989_);
v_a_2079_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2064_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2064_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
v___jp_2087_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_unsigned_to_nat(2u);
v___x_2089_ = l_Lean_Syntax_getArg(v_x_1974_, v___x_2088_);
lean_dec(v_x_1974_);
if (v___x_1984_ == 0)
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v___x_2089_);
v___x_2091_ = l_Lean_Syntax_isOfKind(v___x_2089_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec(v___x_2089_);
lean_dec(v_docs_1989_);
v___x_2092_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3);
v___x_2093_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_2092_, v_a_1975_, v_a_1976_);
return v___x_2093_;
}
else
{
v___y_2061_ = v___x_2089_;
goto v___jp_2060_;
}
}
else
{
v___y_2061_ = v___x_2089_;
goto v___jp_2060_;
}
}
}
}
else
{
lean_object* v___x_2098_; lean_object* v_cmd_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec(v___x_1983_);
v___x_2098_ = lean_unsigned_to_nat(1u);
v_cmd_2099_ = l_Lean_Syntax_getArg(v_x_1974_, v___x_2098_);
lean_dec(v_x_1974_);
v___x_2100_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15);
v___x_2101_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__0_spec__0___redArg(v_cmd_2099_, v___x_2100_, v_a_1975_, v_a_1976_);
lean_dec(v_cmd_2099_);
return v___x_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2118_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2119_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_2120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_2121_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_2122_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2118_, v___x_2119_, v___x_2120_, v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_2152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_2153_ = l_Lean_addBuiltinDeclarationRanges(v___x_2151_, v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_2155_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_2158_ = l_Lean_stringToMessageData(v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v_a_2176_; lean_object* v_doc_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_2168_);
v___x_2246_ = l_Lean_Syntax_isOfKind(v_x_2168_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec(v_x_2168_);
v___x_2247_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_2248_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_2247_, v_a_2169_, v_a_2170_);
return v___x_2248_;
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v___x_2249_ = lean_unsigned_to_nat(0u);
v___x_2250_ = l_Lean_Syntax_getArg(v_x_2168_, v___x_2249_);
v___x_2251_ = l_Lean_Syntax_isNone(v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_2250_);
v___x_2253_ = l_Lean_Syntax_matchesNull(v___x_2250_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec(v___x_2250_);
lean_dec(v_x_2168_);
v___x_2254_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_2255_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_2254_, v_a_2169_, v_a_2170_);
return v___x_2255_;
}
else
{
lean_object* v_doc_2256_; 
v_doc_2256_ = l_Lean_Syntax_getArg(v___x_2250_, v___x_2249_);
lean_dec(v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
lean_inc(v_doc_2256_);
v___x_2260_ = l_Lean_Syntax_isOfKind(v_doc_2256_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v_doc_2256_);
lean_dec(v_x_2168_);
v___x_2261_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_2262_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_2261_, v_a_2169_, v_a_2170_);
return v___x_2262_;
}
else
{
goto v___jp_2257_;
}
}
else
{
goto v___jp_2257_;
}
v___jp_2257_:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v_doc_2256_);
v_doc_2211_ = v___x_2258_;
v___y_2212_ = v_a_2169_;
v___y_2213_ = v_a_2170_;
goto v___jp_2210_;
}
}
}
else
{
lean_object* v___x_2263_; 
lean_dec(v___x_2250_);
v___x_2263_ = lean_box(0);
v_doc_2211_ = v___x_2263_;
v___y_2212_ = v_a_2169_;
v___y_2213_ = v_a_2170_;
goto v___jp_2210_;
}
}
v___jp_2172_:
{
lean_object* v___x_2177_; lean_object* v_env_2178_; lean_object* v_messages_2179_; lean_object* v_scopes_2180_; lean_object* v_usedQuotCtxts_2181_; lean_object* v_nextMacroScope_2182_; lean_object* v_maxRecDepth_2183_; lean_object* v_ngen_2184_; lean_object* v_auxDeclNGen_2185_; lean_object* v_infoState_2186_; lean_object* v_traceState_2187_; lean_object* v_snapshotTasks_2188_; lean_object* v_prevLinterStates_2189_; lean_object* v_codeQualityEntryTasks_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2209_; 
v___x_2177_ = lean_st_ref_take(v___y_2175_);
v_env_2178_ = lean_ctor_get(v___x_2177_, 0);
v_messages_2179_ = lean_ctor_get(v___x_2177_, 1);
v_scopes_2180_ = lean_ctor_get(v___x_2177_, 2);
v_usedQuotCtxts_2181_ = lean_ctor_get(v___x_2177_, 3);
v_nextMacroScope_2182_ = lean_ctor_get(v___x_2177_, 4);
v_maxRecDepth_2183_ = lean_ctor_get(v___x_2177_, 5);
v_ngen_2184_ = lean_ctor_get(v___x_2177_, 6);
v_auxDeclNGen_2185_ = lean_ctor_get(v___x_2177_, 7);
v_infoState_2186_ = lean_ctor_get(v___x_2177_, 8);
v_traceState_2187_ = lean_ctor_get(v___x_2177_, 9);
v_snapshotTasks_2188_ = lean_ctor_get(v___x_2177_, 10);
v_prevLinterStates_2189_ = lean_ctor_get(v___x_2177_, 11);
v_codeQualityEntryTasks_2190_ = lean_ctor_get(v___x_2177_, 12);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2192_ = v___x_2177_;
v_isShared_2193_ = v_isSharedCheck_2209_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2190_);
lean_inc(v_prevLinterStates_2189_);
lean_inc(v_snapshotTasks_2188_);
lean_inc(v_traceState_2187_);
lean_inc(v_infoState_2186_);
lean_inc(v_auxDeclNGen_2185_);
lean_inc(v_ngen_2184_);
lean_inc(v_maxRecDepth_2183_);
lean_inc(v_nextMacroScope_2182_);
lean_inc(v_usedQuotCtxts_2181_);
lean_inc(v_scopes_2180_);
lean_inc(v_messages_2179_);
lean_inc(v_env_2178_);
lean_dec(v___x_2177_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2209_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v_toEnvExtension_2195_; lean_object* v_asyncMode_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2194_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2195_ = lean_ctor_get(v___x_2194_, 0);
v_asyncMode_2196_ = lean_ctor_get(v_toEnvExtension_2195_, 2);
v___x_2197_ = lean_box(0);
v___x_2198_ = l_Lean_TSyntax_getId(v___y_2173_);
lean_dec(v___y_2173_);
v___x_2199_ = l_Lean_TSyntax_getString(v___y_2174_);
lean_dec(v___y_2174_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v_a_2176_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2198_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_box(0);
v___x_2203_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2194_, v_env_2178_, v___x_2201_, v_asyncMode_2196_, v___x_2202_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2203_);
v___x_2205_ = v___x_2192_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_messages_2179_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_scopes_2180_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_usedQuotCtxts_2181_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_nextMacroScope_2182_);
lean_ctor_set(v_reuseFailAlloc_2208_, 5, v_maxRecDepth_2183_);
lean_ctor_set(v_reuseFailAlloc_2208_, 6, v_ngen_2184_);
lean_ctor_set(v_reuseFailAlloc_2208_, 7, v_auxDeclNGen_2185_);
lean_ctor_set(v_reuseFailAlloc_2208_, 8, v_infoState_2186_);
lean_ctor_set(v_reuseFailAlloc_2208_, 9, v_traceState_2187_);
lean_ctor_set(v_reuseFailAlloc_2208_, 10, v_snapshotTasks_2188_);
lean_ctor_set(v_reuseFailAlloc_2208_, 11, v_prevLinterStates_2189_);
lean_ctor_set(v_reuseFailAlloc_2208_, 12, v_codeQualityEntryTasks_2190_);
v___x_2205_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = lean_st_ref_put(v___y_2175_, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2197_);
return v___x_2207_;
}
}
}
v___jp_2210_:
{
lean_object* v___x_2214_; lean_object* v_tag_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2214_ = lean_unsigned_to_nat(2u);
v_tag_2215_ = l_Lean_Syntax_getArg(v_x_2168_, v___x_2214_);
v___x_2216_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
lean_inc(v_tag_2215_);
v___x_2217_ = l_Lean_Syntax_isOfKind(v_tag_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v_tag_2215_);
lean_dec(v_doc_2211_);
lean_dec(v_x_2168_);
v___x_2218_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_2219_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_2218_, v___y_2212_, v___y_2213_);
return v___x_2219_;
}
else
{
lean_object* v___x_2220_; lean_object* v_user_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2220_ = lean_unsigned_to_nat(3u);
v_user_2221_ = l_Lean_Syntax_getArg(v_x_2168_, v___x_2220_);
lean_dec(v_x_2168_);
v___x_2222_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_2221_);
v___x_2223_ = l_Lean_Syntax_isOfKind(v_user_2221_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v_user_2221_);
lean_dec(v_tag_2215_);
lean_dec(v_doc_2211_);
v___x_2224_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_2225_ = l_Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3___redArg(v___x_2224_, v___y_2212_, v___y_2213_);
return v___x_2225_;
}
else
{
if (lean_obj_tag(v_doc_2211_) == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_box(0);
v___y_2173_ = v_tag_2215_;
v___y_2174_ = v_user_2221_;
v___y_2175_ = v___y_2213_;
v_a_2176_ = v___x_2226_;
goto v___jp_2172_;
}
else
{
lean_object* v_val_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2244_; 
v_val_2227_ = lean_ctor_get(v_doc_2211_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_doc_2211_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2229_ = v_doc_2211_;
v_isShared_2230_ = v_isSharedCheck_2244_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_val_2227_);
lean_dec(v_doc_2211_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2244_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; 
v___x_2231_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown(v_val_2227_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v_a_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
v___y_2173_ = v_tag_2215_;
v___y_2174_ = v_user_2221_;
v___y_2175_ = v___y_2213_;
v_a_2176_ = v___x_2234_;
goto v___jp_2172_;
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_del_object(v___x_2229_);
lean_dec(v_user_2221_);
lean_dec(v_tag_2215_);
v_a_2236_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2231_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2231_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2277_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2278_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_2279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_2280_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_2281_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2277_, v___x_2278_, v___x_2279_, v___x_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_2312_ = l_Lean_addBuiltinDeclarationRanges(v___x_2310_, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_2315_, lean_object* v_x_2316_){
_start:
{
if (lean_obj_tag(v_x_2316_) == 0)
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
return v___x_2317_;
}
else
{
lean_dec_ref(v___x_2315_);
lean_inc_ref(v_x_2316_);
return v_x_2316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_2318_, lean_object* v_x_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2318_, v_x_2319_);
lean_dec(v_x_2319_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_2321_, lean_object* v_k_2322_, lean_object* v_t_2323_){
_start:
{
if (lean_obj_tag(v_t_2323_) == 0)
{
lean_object* v_size_2324_; lean_object* v_k_2325_; lean_object* v_v_2326_; lean_object* v_l_2327_; lean_object* v_r_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2654_; 
v_size_2324_ = lean_ctor_get(v_t_2323_, 0);
v_k_2325_ = lean_ctor_get(v_t_2323_, 1);
v_v_2326_ = lean_ctor_get(v_t_2323_, 2);
v_l_2327_ = lean_ctor_get(v_t_2323_, 3);
v_r_2328_ = lean_ctor_get(v_t_2323_, 4);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_t_2323_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2330_ = v_t_2323_;
v_isShared_2331_ = v_isSharedCheck_2654_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_r_2328_);
lean_inc(v_l_2327_);
lean_inc(v_v_2326_);
lean_inc(v_k_2325_);
lean_inc(v_size_2324_);
lean_dec(v_t_2323_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2654_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
uint8_t v___x_2332_; 
v___x_2332_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2322_, v_k_2325_);
switch(v___x_2332_)
{
case 0:
{
lean_object* v_impl_2333_; lean_object* v___x_2334_; 
lean_del_object(v___x_2330_);
lean_dec(v_size_2324_);
v_impl_2333_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2321_, v_k_2322_, v_l_2327_);
v___x_2334_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2325_, v_v_2326_, v_impl_2333_, v_r_2328_);
return v___x_2334_;
}
case 1:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v_k_2325_);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v_v_2326_);
v___x_2336_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2321_, v___x_2335_);
lean_dec_ref_known(v___x_2335_, 1);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_del_object(v___x_2330_);
lean_dec(v_size_2324_);
lean_dec(v_k_2322_);
if (lean_obj_tag(v_l_2327_) == 0)
{
if (lean_obj_tag(v_r_2328_) == 0)
{
lean_object* v_size_2337_; lean_object* v_k_2338_; lean_object* v_v_2339_; lean_object* v_l_2340_; lean_object* v_r_2341_; lean_object* v_size_2342_; lean_object* v_k_2343_; lean_object* v_v_2344_; lean_object* v_l_2345_; lean_object* v_r_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_size_2337_ = lean_ctor_get(v_l_2327_, 0);
v_k_2338_ = lean_ctor_get(v_l_2327_, 1);
v_v_2339_ = lean_ctor_get(v_l_2327_, 2);
v_l_2340_ = lean_ctor_get(v_l_2327_, 3);
v_r_2341_ = lean_ctor_get(v_l_2327_, 4);
lean_inc(v_r_2341_);
v_size_2342_ = lean_ctor_get(v_r_2328_, 0);
v_k_2343_ = lean_ctor_get(v_r_2328_, 1);
v_v_2344_ = lean_ctor_get(v_r_2328_, 2);
v_l_2345_ = lean_ctor_get(v_r_2328_, 3);
lean_inc(v_l_2345_);
v_r_2346_ = lean_ctor_get(v_r_2328_, 4);
v___x_2347_ = lean_unsigned_to_nat(1u);
v___x_2348_ = lean_nat_dec_lt(v_size_2337_, v_size_2342_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2484_; 
lean_inc(v_l_2340_);
lean_inc(v_v_2339_);
lean_inc(v_k_2338_);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_l_2327_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; lean_object* v_unused_2486_; lean_object* v_unused_2487_; lean_object* v_unused_2488_; lean_object* v_unused_2489_; 
v_unused_2485_ = lean_ctor_get(v_l_2327_, 4);
lean_dec(v_unused_2485_);
v_unused_2486_ = lean_ctor_get(v_l_2327_, 3);
lean_dec(v_unused_2486_);
v_unused_2487_ = lean_ctor_get(v_l_2327_, 2);
lean_dec(v_unused_2487_);
v_unused_2488_ = lean_ctor_get(v_l_2327_, 1);
lean_dec(v_unused_2488_);
v_unused_2489_ = lean_ctor_get(v_l_2327_, 0);
lean_dec(v_unused_2489_);
v___x_2350_ = v_l_2327_;
v_isShared_2351_ = v_isSharedCheck_2484_;
goto v_resetjp_2349_;
}
else
{
lean_dec(v_l_2327_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2484_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v_tree_2353_; 
v___x_2352_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2338_, v_v_2339_, v_l_2340_, v_r_2341_);
v_tree_2353_ = lean_ctor_get(v___x_2352_, 2);
lean_inc(v_tree_2353_);
if (lean_obj_tag(v_tree_2353_) == 0)
{
lean_object* v_k_2354_; lean_object* v_v_2355_; lean_object* v_size_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v_k_2354_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_k_2354_);
v_v_2355_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_v_2355_);
lean_dec_ref(v___x_2352_);
v_size_2356_ = lean_ctor_get(v_tree_2353_, 0);
v___x_2357_ = lean_unsigned_to_nat(3u);
v___x_2358_ = lean_nat_mul(v___x_2357_, v_size_2356_);
v___x_2359_ = lean_nat_dec_lt(v___x_2358_, v_size_2342_);
lean_dec(v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec(v_l_2345_);
v___x_2360_ = lean_nat_add(v___x_2347_, v_size_2356_);
v___x_2361_ = lean_nat_add(v___x_2360_, v_size_2342_);
lean_dec(v___x_2360_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v_r_2328_);
lean_ctor_set(v___x_2350_, 3, v_tree_2353_);
lean_ctor_set(v___x_2350_, 2, v_v_2355_);
lean_ctor_set(v___x_2350_, 1, v_k_2354_);
lean_ctor_set(v___x_2350_, 0, v___x_2361_);
v___x_2363_ = v___x_2350_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_k_2354_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_v_2355_);
lean_ctor_set(v_reuseFailAlloc_2364_, 3, v_tree_2353_);
lean_ctor_set(v_reuseFailAlloc_2364_, 4, v_r_2328_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
else
{
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2419_; 
lean_inc(v_r_2346_);
lean_inc(v_v_2344_);
lean_inc(v_k_2343_);
lean_inc(v_size_2342_);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_r_2328_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; lean_object* v_unused_2421_; lean_object* v_unused_2422_; lean_object* v_unused_2423_; lean_object* v_unused_2424_; 
v_unused_2420_ = lean_ctor_get(v_r_2328_, 4);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_r_2328_, 3);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_r_2328_, 2);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_r_2328_, 1);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_r_2328_, 0);
lean_dec(v_unused_2424_);
v___x_2366_ = v_r_2328_;
v_isShared_2367_ = v_isSharedCheck_2419_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v_r_2328_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2419_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_size_2368_; lean_object* v_k_2369_; lean_object* v_v_2370_; lean_object* v_l_2371_; lean_object* v_r_2372_; lean_object* v_size_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v_size_2368_ = lean_ctor_get(v_l_2345_, 0);
v_k_2369_ = lean_ctor_get(v_l_2345_, 1);
v_v_2370_ = lean_ctor_get(v_l_2345_, 2);
v_l_2371_ = lean_ctor_get(v_l_2345_, 3);
v_r_2372_ = lean_ctor_get(v_l_2345_, 4);
v_size_2373_ = lean_ctor_get(v_r_2346_, 0);
v___x_2374_ = lean_unsigned_to_nat(2u);
v___x_2375_ = lean_nat_mul(v___x_2374_, v_size_2373_);
v___x_2376_ = lean_nat_dec_lt(v_size_2368_, v___x_2375_);
lean_dec(v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2404_; 
lean_inc(v_r_2372_);
lean_inc(v_l_2371_);
lean_inc(v_v_2370_);
lean_inc(v_k_2369_);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_l_2345_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; lean_object* v_unused_2406_; lean_object* v_unused_2407_; lean_object* v_unused_2408_; lean_object* v_unused_2409_; 
v_unused_2405_ = lean_ctor_get(v_l_2345_, 4);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_l_2345_, 3);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_l_2345_, 2);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_l_2345_, 1);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_l_2345_, 0);
lean_dec(v_unused_2409_);
v___x_2378_ = v_l_2345_;
v_isShared_2379_ = v_isSharedCheck_2404_;
goto v_resetjp_2377_;
}
else
{
lean_dec(v_l_2345_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2404_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2394_; 
v___x_2380_ = lean_nat_add(v___x_2347_, v_size_2356_);
v___x_2381_ = lean_nat_add(v___x_2380_, v_size_2342_);
lean_dec(v_size_2342_);
if (lean_obj_tag(v_l_2371_) == 0)
{
lean_object* v_size_2402_; 
v_size_2402_ = lean_ctor_get(v_l_2371_, 0);
lean_inc(v_size_2402_);
v___y_2394_ = v_size_2402_;
goto v___jp_2393_;
}
else
{
lean_object* v___x_2403_; 
v___x_2403_ = lean_unsigned_to_nat(0u);
v___y_2394_ = v___x_2403_;
goto v___jp_2393_;
}
v___jp_2382_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_nat_add(v___y_2383_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec(v___y_2383_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 4, v_r_2346_);
lean_ctor_set(v___x_2378_, 3, v_r_2372_);
lean_ctor_set(v___x_2378_, 2, v_v_2344_);
lean_ctor_set(v___x_2378_, 1, v_k_2343_);
lean_ctor_set(v___x_2378_, 0, v___x_2386_);
v___x_2388_ = v___x_2378_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_k_2343_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_v_2344_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_r_2372_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_r_2346_);
v___x_2388_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 4, v___x_2388_);
lean_ctor_set(v___x_2366_, 3, v___y_2384_);
lean_ctor_set(v___x_2366_, 2, v_v_2370_);
lean_ctor_set(v___x_2366_, 1, v_k_2369_);
lean_ctor_set(v___x_2366_, 0, v___x_2381_);
v___x_2390_ = v___x_2366_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_k_2369_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v_v_2370_);
lean_ctor_set(v_reuseFailAlloc_2391_, 3, v___y_2384_);
lean_ctor_set(v_reuseFailAlloc_2391_, 4, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
v___jp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = lean_nat_add(v___x_2380_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec(v___x_2380_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v_l_2371_);
lean_ctor_set(v___x_2350_, 3, v_tree_2353_);
lean_ctor_set(v___x_2350_, 2, v_v_2355_);
lean_ctor_set(v___x_2350_, 1, v_k_2354_);
lean_ctor_set(v___x_2350_, 0, v___x_2395_);
v___x_2397_ = v___x_2350_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_k_2354_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_v_2355_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_tree_2353_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_l_2371_);
v___x_2397_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_nat_add(v___x_2347_, v_size_2373_);
if (lean_obj_tag(v_r_2372_) == 0)
{
lean_object* v_size_2399_; 
v_size_2399_ = lean_ctor_get(v_r_2372_, 0);
lean_inc(v_size_2399_);
v___y_2383_ = v___x_2398_;
v___y_2384_ = v___x_2397_;
v___y_2385_ = v_size_2399_;
goto v___jp_2382_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_unsigned_to_nat(0u);
v___y_2383_ = v___x_2398_;
v___y_2384_ = v___x_2397_;
v___y_2385_ = v___x_2400_;
goto v___jp_2382_;
}
}
}
}
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2410_ = lean_nat_add(v___x_2347_, v_size_2356_);
v___x_2411_ = lean_nat_add(v___x_2410_, v_size_2342_);
lean_dec(v_size_2342_);
v___x_2412_ = lean_nat_add(v___x_2410_, v_size_2368_);
lean_dec(v___x_2410_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 4, v_l_2345_);
lean_ctor_set(v___x_2366_, 3, v_tree_2353_);
lean_ctor_set(v___x_2366_, 2, v_v_2355_);
lean_ctor_set(v___x_2366_, 1, v_k_2354_);
lean_ctor_set(v___x_2366_, 0, v___x_2412_);
v___x_2414_ = v___x_2366_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_k_2354_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_v_2355_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_tree_2353_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_l_2345_);
v___x_2414_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v_r_2346_);
lean_ctor_set(v___x_2350_, 3, v___x_2414_);
lean_ctor_set(v___x_2350_, 2, v_v_2344_);
lean_ctor_set(v___x_2350_, 1, v_k_2343_);
lean_ctor_set(v___x_2350_, 0, v___x_2411_);
v___x_2416_ = v___x_2350_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_k_2343_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_v_2344_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v_r_2346_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
else
{
lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2478_; 
lean_inc(v_r_2346_);
lean_inc(v_v_2344_);
lean_inc(v_k_2343_);
lean_inc(v_size_2342_);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_r_2328_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; lean_object* v_unused_2480_; lean_object* v_unused_2481_; lean_object* v_unused_2482_; lean_object* v_unused_2483_; 
v_unused_2479_ = lean_ctor_get(v_r_2328_, 4);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_r_2328_, 3);
lean_dec(v_unused_2480_);
v_unused_2481_ = lean_ctor_get(v_r_2328_, 2);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v_r_2328_, 1);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_r_2328_, 0);
lean_dec(v_unused_2483_);
v___x_2426_ = v_r_2328_;
v_isShared_2427_ = v_isSharedCheck_2478_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v_r_2328_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2478_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
if (lean_obj_tag(v_l_2345_) == 0)
{
if (lean_obj_tag(v_r_2346_) == 0)
{
lean_object* v_k_2428_; lean_object* v_v_2429_; lean_object* v_size_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v_k_2428_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_k_2428_);
v_v_2429_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_v_2429_);
lean_dec_ref(v___x_2352_);
v_size_2430_ = lean_ctor_get(v_l_2345_, 0);
v___x_2431_ = lean_nat_add(v___x_2347_, v_size_2342_);
lean_dec(v_size_2342_);
v___x_2432_ = lean_nat_add(v___x_2347_, v_size_2430_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 4, v_l_2345_);
lean_ctor_set(v___x_2426_, 3, v_tree_2353_);
lean_ctor_set(v___x_2426_, 2, v_v_2429_);
lean_ctor_set(v___x_2426_, 1, v_k_2428_);
lean_ctor_set(v___x_2426_, 0, v___x_2432_);
v___x_2434_ = v___x_2426_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2438_, 3, v_tree_2353_);
lean_ctor_set(v_reuseFailAlloc_2438_, 4, v_l_2345_);
v___x_2434_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2436_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v_r_2346_);
lean_ctor_set(v___x_2350_, 3, v___x_2434_);
lean_ctor_set(v___x_2350_, 2, v_v_2344_);
lean_ctor_set(v___x_2350_, 1, v_k_2343_);
lean_ctor_set(v___x_2350_, 0, v___x_2431_);
v___x_2436_ = v___x_2350_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_k_2343_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_v_2344_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_r_2346_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
else
{
lean_object* v_k_2439_; lean_object* v_v_2440_; lean_object* v_k_2441_; lean_object* v_v_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_size_2342_);
v_k_2439_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_k_2439_);
v_v_2440_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_v_2440_);
lean_dec_ref(v___x_2352_);
v_k_2441_ = lean_ctor_get(v_l_2345_, 1);
v_v_2442_ = lean_ctor_get(v_l_2345_, 2);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_l_2345_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; lean_object* v_unused_2458_; lean_object* v_unused_2459_; 
v_unused_2457_ = lean_ctor_get(v_l_2345_, 4);
lean_dec(v_unused_2457_);
v_unused_2458_ = lean_ctor_get(v_l_2345_, 3);
lean_dec(v_unused_2458_);
v_unused_2459_ = lean_ctor_get(v_l_2345_, 0);
lean_dec(v_unused_2459_);
v___x_2444_ = v_l_2345_;
v_isShared_2445_ = v_isSharedCheck_2456_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_v_2442_);
lean_inc(v_k_2441_);
lean_dec(v_l_2345_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2456_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_unsigned_to_nat(3u);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 4, v_r_2346_);
lean_ctor_set(v___x_2444_, 3, v_r_2346_);
lean_ctor_set(v___x_2444_, 2, v_v_2440_);
lean_ctor_set(v___x_2444_, 1, v_k_2439_);
lean_ctor_set(v___x_2444_, 0, v___x_2347_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_r_2346_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_r_2346_);
v___x_2448_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2450_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 3, v_r_2346_);
lean_ctor_set(v___x_2426_, 0, v___x_2347_);
v___x_2450_ = v___x_2426_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_k_2343_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v_v_2344_);
lean_ctor_set(v_reuseFailAlloc_2454_, 3, v_r_2346_);
lean_ctor_set(v_reuseFailAlloc_2454_, 4, v_r_2346_);
v___x_2450_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v___x_2450_);
lean_ctor_set(v___x_2350_, 3, v___x_2448_);
lean_ctor_set(v___x_2350_, 2, v_v_2442_);
lean_ctor_set(v___x_2350_, 1, v_k_2441_);
lean_ctor_set(v___x_2350_, 0, v___x_2446_);
v___x_2452_ = v___x_2350_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_k_2441_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v_v_2442_);
lean_ctor_set(v_reuseFailAlloc_2453_, 3, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2453_, 4, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2346_) == 0)
{
lean_object* v_k_2460_; lean_object* v_v_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
lean_dec(v_size_2342_);
v_k_2460_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_k_2460_);
v_v_2461_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_v_2461_);
lean_dec_ref(v___x_2352_);
v___x_2462_ = lean_unsigned_to_nat(3u);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 4, v_l_2345_);
lean_ctor_set(v___x_2426_, 2, v_v_2461_);
lean_ctor_set(v___x_2426_, 1, v_k_2460_);
lean_ctor_set(v___x_2426_, 0, v___x_2347_);
v___x_2464_ = v___x_2426_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_k_2460_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_v_2461_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_l_2345_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_l_2345_);
v___x_2464_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2466_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v_r_2346_);
lean_ctor_set(v___x_2350_, 3, v___x_2464_);
lean_ctor_set(v___x_2350_, 2, v_v_2344_);
lean_ctor_set(v___x_2350_, 1, v_k_2343_);
lean_ctor_set(v___x_2350_, 0, v___x_2462_);
v___x_2466_ = v___x_2350_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_k_2343_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_v_2344_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_r_2346_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_k_2469_; lean_object* v_v_2470_; lean_object* v___x_2472_; 
v_k_2469_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_k_2469_);
v_v_2470_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_v_2470_);
lean_dec_ref(v___x_2352_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 3, v_r_2346_);
v___x_2472_ = v___x_2426_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_size_2342_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_k_2343_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_v_2344_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_r_2346_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_r_2346_);
v___x_2472_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_unsigned_to_nat(2u);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v___x_2472_);
lean_ctor_set(v___x_2350_, 3, v_r_2346_);
lean_ctor_set(v___x_2350_, 2, v_v_2470_);
lean_ctor_set(v___x_2350_, 1, v_k_2469_);
lean_ctor_set(v___x_2350_, 0, v___x_2473_);
v___x_2475_ = v___x_2350_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_k_2469_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_v_2470_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_r_2346_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v___x_2472_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
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
lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2642_; 
lean_inc(v_r_2346_);
lean_inc(v_v_2344_);
lean_inc(v_k_2343_);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_r_2328_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; lean_object* v_unused_2644_; lean_object* v_unused_2645_; lean_object* v_unused_2646_; lean_object* v_unused_2647_; 
v_unused_2643_ = lean_ctor_get(v_r_2328_, 4);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v_r_2328_, 3);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v_r_2328_, 2);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_r_2328_, 1);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_r_2328_, 0);
lean_dec(v_unused_2647_);
v___x_2491_ = v_r_2328_;
v_isShared_2492_ = v_isSharedCheck_2642_;
goto v_resetjp_2490_;
}
else
{
lean_dec(v_r_2328_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2642_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v_tree_2494_; 
v___x_2493_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2343_, v_v_2344_, v_l_2345_, v_r_2346_);
v_tree_2494_ = lean_ctor_get(v___x_2493_, 2);
lean_inc(v_tree_2494_);
if (lean_obj_tag(v_tree_2494_) == 0)
{
lean_object* v_k_2495_; lean_object* v_v_2496_; lean_object* v_size_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_k_2495_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_k_2495_);
v_v_2496_ = lean_ctor_get(v___x_2493_, 1);
lean_inc(v_v_2496_);
lean_dec_ref(v___x_2493_);
v_size_2497_ = lean_ctor_get(v_tree_2494_, 0);
v___x_2498_ = lean_unsigned_to_nat(3u);
v___x_2499_ = lean_nat_mul(v___x_2498_, v_size_2497_);
v___x_2500_ = lean_nat_dec_lt(v___x_2499_, v_size_2337_);
lean_dec(v___x_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_dec(v_r_2341_);
v___x_2501_ = lean_nat_add(v___x_2347_, v_size_2337_);
v___x_2502_ = lean_nat_add(v___x_2501_, v_size_2497_);
lean_dec(v___x_2501_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v_tree_2494_);
lean_ctor_set(v___x_2491_, 3, v_l_2327_);
lean_ctor_set(v___x_2491_, 2, v_v_2496_);
lean_ctor_set(v___x_2491_, 1, v_k_2495_);
lean_ctor_set(v___x_2491_, 0, v___x_2502_);
v___x_2504_ = v___x_2491_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_k_2495_);
lean_ctor_set(v_reuseFailAlloc_2505_, 2, v_v_2496_);
lean_ctor_set(v_reuseFailAlloc_2505_, 3, v_l_2327_);
lean_ctor_set(v_reuseFailAlloc_2505_, 4, v_tree_2494_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
else
{
lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2571_; 
lean_inc(v_l_2340_);
lean_inc(v_v_2339_);
lean_inc(v_k_2338_);
lean_inc(v_size_2337_);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_l_2327_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; lean_object* v_unused_2573_; lean_object* v_unused_2574_; lean_object* v_unused_2575_; lean_object* v_unused_2576_; 
v_unused_2572_ = lean_ctor_get(v_l_2327_, 4);
lean_dec(v_unused_2572_);
v_unused_2573_ = lean_ctor_get(v_l_2327_, 3);
lean_dec(v_unused_2573_);
v_unused_2574_ = lean_ctor_get(v_l_2327_, 2);
lean_dec(v_unused_2574_);
v_unused_2575_ = lean_ctor_get(v_l_2327_, 1);
lean_dec(v_unused_2575_);
v_unused_2576_ = lean_ctor_get(v_l_2327_, 0);
lean_dec(v_unused_2576_);
v___x_2507_ = v_l_2327_;
v_isShared_2508_ = v_isSharedCheck_2571_;
goto v_resetjp_2506_;
}
else
{
lean_dec(v_l_2327_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2571_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v_size_2509_; lean_object* v_size_2510_; lean_object* v_k_2511_; lean_object* v_v_2512_; lean_object* v_l_2513_; lean_object* v_r_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_size_2509_ = lean_ctor_get(v_l_2340_, 0);
v_size_2510_ = lean_ctor_get(v_r_2341_, 0);
v_k_2511_ = lean_ctor_get(v_r_2341_, 1);
v_v_2512_ = lean_ctor_get(v_r_2341_, 2);
v_l_2513_ = lean_ctor_get(v_r_2341_, 3);
v_r_2514_ = lean_ctor_get(v_r_2341_, 4);
v___x_2515_ = lean_unsigned_to_nat(2u);
v___x_2516_ = lean_nat_mul(v___x_2515_, v_size_2509_);
v___x_2517_ = lean_nat_dec_lt(v_size_2510_, v___x_2516_);
lean_dec(v___x_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2555_; 
lean_inc(v_r_2514_);
lean_inc(v_l_2513_);
lean_inc(v_v_2512_);
lean_inc(v_k_2511_);
lean_del_object(v___x_2507_);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_r_2341_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; lean_object* v_unused_2557_; lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; 
v_unused_2556_ = lean_ctor_get(v_r_2341_, 4);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_r_2341_, 3);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_r_2341_, 2);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_r_2341_, 1);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_r_2341_, 0);
lean_dec(v_unused_2560_);
v___x_2519_ = v_r_2341_;
v_isShared_2520_ = v_isSharedCheck_2555_;
goto v_resetjp_2518_;
}
else
{
lean_dec(v_r_2341_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2555_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___x_2543_; lean_object* v___y_2545_; 
v___x_2521_ = lean_nat_add(v___x_2347_, v_size_2337_);
lean_dec(v_size_2337_);
v___x_2522_ = lean_nat_add(v___x_2521_, v_size_2497_);
lean_dec(v___x_2521_);
v___x_2543_ = lean_nat_add(v___x_2347_, v_size_2509_);
if (lean_obj_tag(v_l_2513_) == 0)
{
lean_object* v_size_2553_; 
v_size_2553_ = lean_ctor_get(v_l_2513_, 0);
lean_inc(v_size_2553_);
v___y_2545_ = v_size_2553_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_unsigned_to_nat(0u);
v___y_2545_ = v___x_2554_;
goto v___jp_2544_;
}
v___jp_2523_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = lean_nat_add(v___y_2524_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec(v___y_2524_);
lean_inc_ref(v_tree_2494_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 4, v_tree_2494_);
lean_ctor_set(v___x_2519_, 3, v_r_2514_);
lean_ctor_set(v___x_2519_, 2, v_v_2496_);
lean_ctor_set(v___x_2519_, 1, v_k_2495_);
lean_ctor_set(v___x_2519_, 0, v___x_2527_);
v___x_2529_ = v___x_2519_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_k_2495_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_v_2496_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_r_2514_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v_tree_2494_);
v___x_2529_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_isSharedCheck_2536_ = !lean_is_exclusive(v_tree_2494_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; lean_object* v_unused_2541_; 
v_unused_2537_ = lean_ctor_get(v_tree_2494_, 4);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_tree_2494_, 3);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_tree_2494_, 2);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_tree_2494_, 1);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_tree_2494_, 0);
lean_dec(v_unused_2541_);
v___x_2531_ = v_tree_2494_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_dec(v_tree_2494_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 4, v___x_2529_);
lean_ctor_set(v___x_2531_, 3, v___y_2525_);
lean_ctor_set(v___x_2531_, 2, v_v_2512_);
lean_ctor_set(v___x_2531_, 1, v_k_2511_);
lean_ctor_set(v___x_2531_, 0, v___x_2522_);
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_k_2511_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_v_2512_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v___y_2525_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v___x_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
v___jp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2546_ = lean_nat_add(v___x_2543_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec(v___x_2543_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v_l_2513_);
lean_ctor_set(v___x_2491_, 3, v_l_2340_);
lean_ctor_set(v___x_2491_, 2, v_v_2339_);
lean_ctor_set(v___x_2491_, 1, v_k_2338_);
lean_ctor_set(v___x_2491_, 0, v___x_2546_);
v___x_2548_ = v___x_2491_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_k_2338_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_v_2339_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_l_2340_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_l_2513_);
v___x_2548_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_nat_add(v___x_2347_, v_size_2497_);
if (lean_obj_tag(v_r_2514_) == 0)
{
lean_object* v_size_2550_; 
v_size_2550_ = lean_ctor_get(v_r_2514_, 0);
lean_inc(v_size_2550_);
v___y_2524_ = v___x_2549_;
v___y_2525_ = v___x_2548_;
v___y_2526_ = v_size_2550_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_unsigned_to_nat(0u);
v___y_2524_ = v___x_2549_;
v___y_2525_ = v___x_2548_;
v___y_2526_ = v___x_2551_;
goto v___jp_2523_;
}
}
}
}
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2561_ = lean_nat_add(v___x_2347_, v_size_2337_);
lean_dec(v_size_2337_);
v___x_2562_ = lean_nat_add(v___x_2561_, v_size_2497_);
lean_dec(v___x_2561_);
v___x_2563_ = lean_nat_add(v___x_2347_, v_size_2497_);
v___x_2564_ = lean_nat_add(v___x_2563_, v_size_2510_);
lean_dec(v___x_2563_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v_tree_2494_);
lean_ctor_set(v___x_2491_, 3, v_r_2341_);
lean_ctor_set(v___x_2491_, 2, v_v_2496_);
lean_ctor_set(v___x_2491_, 1, v_k_2495_);
lean_ctor_set(v___x_2491_, 0, v___x_2564_);
v___x_2566_ = v___x_2491_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_k_2495_);
lean_ctor_set(v_reuseFailAlloc_2570_, 2, v_v_2496_);
lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_r_2341_);
lean_ctor_set(v_reuseFailAlloc_2570_, 4, v_tree_2494_);
v___x_2566_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 4, v___x_2566_);
lean_ctor_set(v___x_2507_, 0, v___x_2562_);
v___x_2568_ = v___x_2507_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_k_2338_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_v_2339_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_l_2340_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2340_) == 0)
{
lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2600_; 
lean_inc_ref(v_l_2340_);
lean_inc(v_v_2339_);
lean_inc(v_k_2338_);
lean_inc(v_size_2337_);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_l_2327_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; lean_object* v_unused_2602_; lean_object* v_unused_2603_; lean_object* v_unused_2604_; lean_object* v_unused_2605_; 
v_unused_2601_ = lean_ctor_get(v_l_2327_, 4);
lean_dec(v_unused_2601_);
v_unused_2602_ = lean_ctor_get(v_l_2327_, 3);
lean_dec(v_unused_2602_);
v_unused_2603_ = lean_ctor_get(v_l_2327_, 2);
lean_dec(v_unused_2603_);
v_unused_2604_ = lean_ctor_get(v_l_2327_, 1);
lean_dec(v_unused_2604_);
v_unused_2605_ = lean_ctor_get(v_l_2327_, 0);
lean_dec(v_unused_2605_);
v___x_2578_ = v_l_2327_;
v_isShared_2579_ = v_isSharedCheck_2600_;
goto v_resetjp_2577_;
}
else
{
lean_dec(v_l_2327_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2600_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
if (lean_obj_tag(v_r_2341_) == 0)
{
lean_object* v_k_2580_; lean_object* v_v_2581_; lean_object* v_size_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v_k_2580_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_k_2580_);
v_v_2581_ = lean_ctor_get(v___x_2493_, 1);
lean_inc(v_v_2581_);
lean_dec_ref(v___x_2493_);
v_size_2582_ = lean_ctor_get(v_r_2341_, 0);
v___x_2583_ = lean_nat_add(v___x_2347_, v_size_2337_);
lean_dec(v_size_2337_);
v___x_2584_ = lean_nat_add(v___x_2347_, v_size_2582_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v_tree_2494_);
lean_ctor_set(v___x_2491_, 3, v_r_2341_);
lean_ctor_set(v___x_2491_, 2, v_v_2581_);
lean_ctor_set(v___x_2491_, 1, v_k_2580_);
lean_ctor_set(v___x_2491_, 0, v___x_2584_);
v___x_2586_ = v___x_2491_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_k_2580_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_v_2581_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_r_2341_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_tree_2494_);
v___x_2586_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2588_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v___x_2586_);
lean_ctor_set(v___x_2578_, 0, v___x_2583_);
v___x_2588_ = v___x_2578_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_k_2338_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_v_2339_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_l_2340_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
lean_object* v_k_2591_; lean_object* v_v_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v_size_2337_);
v_k_2591_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_k_2591_);
v_v_2592_ = lean_ctor_get(v___x_2493_, 1);
lean_inc(v_v_2592_);
lean_dec_ref(v___x_2493_);
v___x_2593_ = lean_unsigned_to_nat(3u);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v_r_2341_);
lean_ctor_set(v___x_2491_, 3, v_r_2341_);
lean_ctor_set(v___x_2491_, 2, v_v_2592_);
lean_ctor_set(v___x_2491_, 1, v_k_2591_);
lean_ctor_set(v___x_2491_, 0, v___x_2347_);
v___x_2595_ = v___x_2491_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_k_2591_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_v_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_r_2341_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_r_2341_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v___x_2595_);
lean_ctor_set(v___x_2578_, 0, v___x_2593_);
v___x_2597_ = v___x_2578_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_2338_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_2339_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_l_2340_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2341_) == 0)
{
lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2630_; 
lean_inc(v_l_2340_);
lean_inc(v_v_2339_);
lean_inc(v_k_2338_);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_l_2327_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; lean_object* v_unused_2635_; 
v_unused_2631_ = lean_ctor_get(v_l_2327_, 4);
lean_dec(v_unused_2631_);
v_unused_2632_ = lean_ctor_get(v_l_2327_, 3);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_l_2327_, 2);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_l_2327_, 1);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_l_2327_, 0);
lean_dec(v_unused_2635_);
v___x_2607_ = v_l_2327_;
v_isShared_2608_ = v_isSharedCheck_2630_;
goto v_resetjp_2606_;
}
else
{
lean_dec(v_l_2327_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2630_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_k_2609_; lean_object* v_v_2610_; lean_object* v_k_2611_; lean_object* v_v_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2626_; 
v_k_2609_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_k_2609_);
v_v_2610_ = lean_ctor_get(v___x_2493_, 1);
lean_inc(v_v_2610_);
lean_dec_ref(v___x_2493_);
v_k_2611_ = lean_ctor_get(v_r_2341_, 1);
v_v_2612_ = lean_ctor_get(v_r_2341_, 2);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_r_2341_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; lean_object* v_unused_2628_; lean_object* v_unused_2629_; 
v_unused_2627_ = lean_ctor_get(v_r_2341_, 4);
lean_dec(v_unused_2627_);
v_unused_2628_ = lean_ctor_get(v_r_2341_, 3);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_r_2341_, 0);
lean_dec(v_unused_2629_);
v___x_2614_ = v_r_2341_;
v_isShared_2615_ = v_isSharedCheck_2626_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_v_2612_);
lean_inc(v_k_2611_);
lean_dec(v_r_2341_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2626_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2616_ = lean_unsigned_to_nat(3u);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 4, v_l_2340_);
lean_ctor_set(v___x_2614_, 3, v_l_2340_);
lean_ctor_set(v___x_2614_, 2, v_v_2339_);
lean_ctor_set(v___x_2614_, 1, v_k_2338_);
lean_ctor_set(v___x_2614_, 0, v___x_2347_);
v___x_2618_ = v___x_2614_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_k_2338_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_v_2339_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_l_2340_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_l_2340_);
v___x_2618_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2620_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v_l_2340_);
lean_ctor_set(v___x_2491_, 3, v_l_2340_);
lean_ctor_set(v___x_2491_, 2, v_v_2610_);
lean_ctor_set(v___x_2491_, 1, v_k_2609_);
lean_ctor_set(v___x_2491_, 0, v___x_2347_);
v___x_2620_ = v___x_2491_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_k_2609_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_v_2610_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_l_2340_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v_l_2340_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 4, v___x_2620_);
lean_ctor_set(v___x_2607_, 3, v___x_2618_);
lean_ctor_set(v___x_2607_, 2, v_v_2612_);
lean_ctor_set(v___x_2607_, 1, v_k_2611_);
lean_ctor_set(v___x_2607_, 0, v___x_2616_);
v___x_2622_ = v___x_2607_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_k_2611_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_v_2612_);
lean_ctor_set(v_reuseFailAlloc_2623_, 3, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2623_, 4, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
else
{
lean_object* v_k_2636_; lean_object* v_v_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v_k_2636_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_k_2636_);
v_v_2637_ = lean_ctor_get(v___x_2493_, 1);
lean_inc(v_v_2637_);
lean_dec_ref(v___x_2493_);
v___x_2638_ = lean_unsigned_to_nat(2u);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v_r_2341_);
lean_ctor_set(v___x_2491_, 3, v_l_2327_);
lean_ctor_set(v___x_2491_, 2, v_v_2637_);
lean_ctor_set(v___x_2491_, 1, v_k_2636_);
lean_ctor_set(v___x_2491_, 0, v___x_2638_);
v___x_2640_ = v___x_2491_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_k_2636_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_v_2637_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_l_2327_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_r_2341_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
}
}
else
{
return v_l_2327_;
}
}
else
{
return v_r_2328_;
}
}
else
{
lean_object* v_val_2648_; lean_object* v___x_2650_; 
v_val_2648_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_val_2648_);
lean_dec_ref_known(v___x_2336_, 1);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 2, v_val_2648_);
lean_ctor_set(v___x_2330_, 1, v_k_2322_);
v___x_2650_ = v___x_2330_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_size_2324_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_k_2322_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_val_2648_);
lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_l_2327_);
lean_ctor_set(v_reuseFailAlloc_2651_, 4, v_r_2328_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
default: 
{
lean_object* v_impl_2652_; lean_object* v___x_2653_; 
lean_del_object(v___x_2330_);
lean_dec(v_size_2324_);
v_impl_2652_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2321_, v_k_2322_, v_r_2328_);
v___x_2653_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_2325_, v_v_2326_, v_l_2327_, v_impl_2652_);
return v___x_2653_;
}
}
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_box(0);
v___x_2656_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_2321_, v___x_2655_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_dec(v_k_2322_);
return v_t_2323_;
}
else
{
lean_object* v_val_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_val_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_val_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = lean_unsigned_to_nat(1u);
v___x_2659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v_k_2322_);
lean_ctor_set(v___x_2659_, 2, v_val_2657_);
lean_ctor_set(v___x_2659_, 3, v_t_2323_);
lean_ctor_set(v___x_2659_, 4, v_t_2323_);
return v___x_2659_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2660_, lean_object* v_i_2661_, lean_object* v_k_2662_){
_start:
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = lean_array_get_size(v_keys_2660_);
v___x_2664_ = lean_nat_dec_lt(v_i_2661_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_dec(v_i_2661_);
return v___x_2664_;
}
else
{
lean_object* v_k_x27_2665_; uint8_t v___x_2666_; 
v_k_x27_2665_ = lean_array_fget_borrowed(v_keys_2660_, v_i_2661_);
v___x_2666_ = lean_name_eq(v_k_2662_, v_k_x27_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_unsigned_to_nat(1u);
v___x_2668_ = lean_nat_add(v_i_2661_, v___x_2667_);
lean_dec(v_i_2661_);
v_i_2661_ = v___x_2668_;
goto _start;
}
else
{
lean_dec(v_i_2661_);
return v___x_2664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2670_, lean_object* v_i_2671_, lean_object* v_k_2672_){
_start:
{
uint8_t v_res_2673_; lean_object* v_r_2674_; 
v_res_2673_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2670_, v_i_2671_, v_k_2672_);
lean_dec(v_k_2672_);
lean_dec_ref(v_keys_2670_);
v_r_2674_ = lean_box(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_2675_, size_t v_x_2676_, lean_object* v_x_2677_){
_start:
{
if (lean_obj_tag(v_x_2675_) == 0)
{
lean_object* v_es_2678_; lean_object* v___x_2679_; size_t v___x_2680_; size_t v___x_2681_; lean_object* v_j_2682_; lean_object* v___x_2683_; 
v_es_2678_ = lean_ctor_get(v_x_2675_, 0);
v___x_2679_ = lean_box(2);
v___x_2680_ = ((size_t)31ULL);
v___x_2681_ = lean_usize_land(v_x_2676_, v___x_2680_);
v_j_2682_ = lean_usize_to_nat(v___x_2681_);
v___x_2683_ = lean_array_get_borrowed(v___x_2679_, v_es_2678_, v_j_2682_);
lean_dec(v_j_2682_);
switch(lean_obj_tag(v___x_2683_))
{
case 0:
{
lean_object* v_key_2684_; uint8_t v___x_2685_; 
v_key_2684_ = lean_ctor_get(v___x_2683_, 0);
v___x_2685_ = lean_name_eq(v_x_2677_, v_key_2684_);
return v___x_2685_;
}
case 1:
{
lean_object* v_node_2686_; size_t v___x_2687_; size_t v___x_2688_; 
v_node_2686_ = lean_ctor_get(v___x_2683_, 0);
v___x_2687_ = ((size_t)5ULL);
v___x_2688_ = lean_usize_shift_right(v_x_2676_, v___x_2687_);
v_x_2675_ = v_node_2686_;
v_x_2676_ = v___x_2688_;
goto _start;
}
default: 
{
uint8_t v___x_2690_; 
v___x_2690_ = 0;
return v___x_2690_;
}
}
}
else
{
lean_object* v_ks_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_ks_2691_ = lean_ctor_get(v_x_2675_, 0);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_2691_, v___x_2692_, v_x_2677_);
return v___x_2693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_2694_, lean_object* v_x_2695_, lean_object* v_x_2696_){
_start:
{
size_t v_x_3827__boxed_2697_; uint8_t v_res_2698_; lean_object* v_r_2699_; 
v_x_3827__boxed_2697_ = lean_unbox_usize(v_x_2695_);
lean_dec(v_x_2695_);
v_res_2698_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2694_, v_x_3827__boxed_2697_, v_x_2696_);
lean_dec(v_x_2696_);
lean_dec_ref(v_x_2694_);
v_r_2699_ = lean_box(v_res_2698_);
return v_r_2699_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_2700_, lean_object* v_x_2701_){
_start:
{
uint64_t v___y_2703_; 
if (lean_obj_tag(v_x_2701_) == 0)
{
uint64_t v___x_2706_; 
v___x_2706_ = 1723ULL;
v___y_2703_ = v___x_2706_;
goto v___jp_2702_;
}
else
{
uint64_t v_hash_2707_; 
v_hash_2707_ = lean_ctor_get_uint64(v_x_2701_, sizeof(void*)*2);
v___y_2703_ = v_hash_2707_;
goto v___jp_2702_;
}
v___jp_2702_:
{
size_t v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = lean_uint64_to_usize(v___y_2703_);
v___x_2705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2700_, v___x_2704_, v_x_2701_);
return v___x_2705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_2708_, lean_object* v_x_2709_){
_start:
{
uint8_t v_res_2710_; lean_object* v_r_2711_; 
v_res_2710_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2708_, v_x_2709_);
lean_dec(v_x_2709_);
lean_dec_ref(v_x_2708_);
v_r_2711_ = lean_box(v_res_2710_);
return v_r_2711_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_2712_, lean_object* v_a_2713_, uint8_t v___x_2714_, lean_object* v_x_2715_, lean_object* v_____s_2716_){
_start:
{
lean_object* v_fst_2717_; lean_object* v_kinds_2718_; uint8_t v___x_2719_; 
v_fst_2717_ = lean_ctor_get(v_x_2715_, 0);
lean_inc(v_fst_2717_);
lean_dec_ref(v_x_2715_);
v_kinds_2718_ = lean_ctor_get(v_tactics_2712_, 1);
v___x_2719_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_2718_, v_fst_2717_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; 
lean_dec(v_fst_2717_);
lean_dec(v_a_2713_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_____s_2716_);
return v___x_2720_;
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = l_Lean_Name_toString(v_a_2713_, v___x_2714_);
v___x_2722_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2721_, v_fst_2717_, v_____s_2716_);
v___x_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_2724_, lean_object* v_a_2725_, lean_object* v___x_2726_, lean_object* v_x_2727_, lean_object* v_____s_2728_){
_start:
{
uint8_t v___x_3883__boxed_2729_; lean_object* v_res_2730_; 
v___x_3883__boxed_2729_ = lean_unbox(v___x_2726_);
v_res_2730_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_2724_, v_a_2725_, v___x_3883__boxed_2729_, v_x_2727_, v_____s_2728_);
lean_dec_ref(v_tactics_2724_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_2731_, lean_object* v_keys_2732_, lean_object* v_vals_2733_, lean_object* v_i_2734_, lean_object* v_acc_2735_){
_start:
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = lean_array_get_size(v_keys_2732_);
v___x_2737_ = lean_nat_dec_lt(v_i_2734_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
lean_dec(v_i_2734_);
lean_dec_ref(v_f_2731_);
v___x_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_acc_2735_);
return v___x_2738_;
}
else
{
lean_object* v_k_2739_; lean_object* v_v_2740_; lean_object* v___x_2741_; 
v_k_2739_ = lean_array_fget_borrowed(v_keys_2732_, v_i_2734_);
v_v_2740_ = lean_array_fget_borrowed(v_vals_2733_, v_i_2734_);
lean_inc_ref(v_f_2731_);
lean_inc(v_v_2740_);
lean_inc(v_k_2739_);
v___x_2741_ = lean_apply_3(v_f_2731_, v_acc_2735_, v_k_2739_, v_v_2740_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_dec(v_i_2734_);
lean_dec_ref(v_f_2731_);
return v___x_2741_;
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2741_, 1);
v___x_2743_ = lean_unsigned_to_nat(1u);
v___x_2744_ = lean_nat_add(v_i_2734_, v___x_2743_);
lean_dec(v_i_2734_);
v_i_2734_ = v___x_2744_;
v_acc_2735_ = v_a_2742_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_2746_, lean_object* v_keys_2747_, lean_object* v_vals_2748_, lean_object* v_i_2749_, lean_object* v_acc_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2746_, v_keys_2747_, v_vals_2748_, v_i_2749_, v_acc_2750_);
lean_dec_ref(v_vals_2748_);
lean_dec_ref(v_keys_2747_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_2752_, lean_object* v_as_2753_, size_t v_i_2754_, size_t v_stop_2755_, lean_object* v_b_2756_){
_start:
{
lean_object* v_a_2758_; lean_object* v___y_2763_; uint8_t v___x_2765_; 
v___x_2765_ = lean_usize_dec_eq(v_i_2754_, v_stop_2755_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_array_uget_borrowed(v_as_2753_, v_i_2754_);
switch(lean_obj_tag(v___x_2766_))
{
case 0:
{
lean_object* v_key_2767_; lean_object* v_val_2768_; lean_object* v___x_2769_; 
v_key_2767_ = lean_ctor_get(v___x_2766_, 0);
v_val_2768_ = lean_ctor_get(v___x_2766_, 1);
lean_inc_ref(v_f_2752_);
lean_inc(v_val_2768_);
lean_inc(v_key_2767_);
v___x_2769_ = lean_apply_3(v_f_2752_, v_b_2756_, v_key_2767_, v_val_2768_);
v___y_2763_ = v___x_2769_;
goto v___jp_2762_;
}
case 1:
{
lean_object* v_node_2770_; lean_object* v___x_2771_; 
v_node_2770_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_node_2770_);
lean_inc_ref(v_f_2752_);
v___x_2771_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2752_, v_node_2770_, v_b_2756_);
v___y_2763_ = v___x_2771_;
goto v___jp_2762_;
}
default: 
{
v_a_2758_ = v_b_2756_;
goto v___jp_2757_;
}
}
}
else
{
lean_object* v___x_2772_; 
lean_dec_ref(v_f_2752_);
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_b_2756_);
return v___x_2772_;
}
v___jp_2757_:
{
size_t v___x_2759_; size_t v___x_2760_; 
v___x_2759_ = ((size_t)1ULL);
v___x_2760_ = lean_usize_add(v_i_2754_, v___x_2759_);
v_i_2754_ = v___x_2760_;
v_b_2756_ = v_a_2758_;
goto _start;
}
v___jp_2762_:
{
if (lean_obj_tag(v___y_2763_) == 0)
{
lean_dec_ref(v_f_2752_);
return v___y_2763_;
}
else
{
lean_object* v_a_2764_; 
v_a_2764_ = lean_ctor_get(v___y_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___y_2763_, 1);
v_a_2758_ = v_a_2764_;
goto v___jp_2757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_){
_start:
{
if (lean_obj_tag(v_x_2774_) == 0)
{
lean_object* v_es_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2789_; 
v_es_2776_ = lean_ctor_get(v_x_2774_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_x_2774_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2778_ = v_x_2774_;
v_isShared_2779_ = v_isSharedCheck_2789_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_es_2776_);
lean_dec(v_x_2774_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2789_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2780_ = lean_unsigned_to_nat(0u);
v___x_2781_ = lean_array_get_size(v_es_2776_);
v___x_2782_ = lean_nat_dec_lt(v___x_2780_, v___x_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2784_; 
lean_dec_ref(v_es_2776_);
lean_dec_ref(v_f_2773_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set_tag(v___x_2778_, 1);
lean_ctor_set(v___x_2778_, 0, v_x_2775_);
v___x_2784_ = v___x_2778_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_x_2775_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
else
{
size_t v___x_2786_; size_t v___x_2787_; lean_object* v___x_2788_; 
lean_del_object(v___x_2778_);
v___x_2786_ = ((size_t)0ULL);
v___x_2787_ = lean_usize_of_nat(v___x_2781_);
v___x_2788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2773_, v_es_2776_, v___x_2786_, v___x_2787_, v_x_2775_);
lean_dec_ref(v_es_2776_);
return v___x_2788_;
}
}
}
else
{
lean_object* v_ks_2790_; lean_object* v_vs_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_ks_2790_ = lean_ctor_get(v_x_2774_, 0);
lean_inc_ref(v_ks_2790_);
v_vs_2791_ = lean_ctor_get(v_x_2774_, 1);
lean_inc_ref(v_vs_2791_);
lean_dec_ref_known(v_x_2774_, 2);
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2773_, v_ks_2790_, v_vs_2791_, v___x_2792_, v_x_2775_);
lean_dec_ref(v_vs_2791_);
lean_dec_ref(v_ks_2790_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_2794_, lean_object* v_as_2795_, lean_object* v_i_2796_, lean_object* v_stop_2797_, lean_object* v_b_2798_){
_start:
{
size_t v_i_boxed_2799_; size_t v_stop_boxed_2800_; lean_object* v_res_2801_; 
v_i_boxed_2799_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_stop_boxed_2800_ = lean_unbox_usize(v_stop_2797_);
lean_dec(v_stop_2797_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2794_, v_as_2795_, v_i_boxed_2799_, v_stop_boxed_2800_, v_b_2798_);
lean_dec_ref(v_as_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_2802_, lean_object* v_s_2803_, lean_object* v_a_2804_, lean_object* v_b_2805_){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_a_2804_);
lean_ctor_set(v___x_2806_, 1, v_b_2805_);
v___x_2807_ = lean_apply_2(v_f_2802_, v___x_2806_, v_s_2803_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2807_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2807_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_2824_, lean_object* v_init_2825_, lean_object* v_f_2826_){
_start:
{
lean_object* v___f_2827_; lean_object* v___x_2828_; lean_object* v_a_2829_; 
v___f_2827_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2827_, 0, v_f_2826_);
lean_inc_ref(v_map_2824_);
v___x_2828_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_2827_, v_map_2824_, v_init_2825_);
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref(v___x_2828_);
return v_a_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_2830_, lean_object* v_init_2831_, lean_object* v_f_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2830_, v_init_2831_, v_f_2832_);
lean_dec_ref(v_map_2830_);
return v_res_2833_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_2836_, lean_object* v_a_2837_, uint8_t v___x_2838_, lean_object* v_as_x27_2839_, lean_object* v_b_2840_){
_start:
{
if (lean_obj_tag(v_as_x27_2839_) == 0)
{
lean_dec(v_a_2837_);
lean_dec_ref(v_tactics_2836_);
return v_b_2840_;
}
else
{
lean_object* v_head_2841_; lean_object* v_fst_2842_; lean_object* v_info_2843_; lean_object* v_tail_2844_; lean_object* v_collectKinds_2845_; lean_object* v___x_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_head_2841_ = lean_ctor_get(v_as_x27_2839_, 0);
v_fst_2842_ = lean_ctor_get(v_head_2841_, 0);
v_info_2843_ = lean_ctor_get(v_fst_2842_, 0);
v_tail_2844_ = lean_ctor_get(v_as_x27_2839_, 1);
v_collectKinds_2845_ = lean_ctor_get(v_info_2843_, 1);
v___x_2846_ = lean_box(v___x_2838_);
lean_inc(v_a_2837_);
lean_inc_ref(v_tactics_2836_);
v___f_2847_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2847_, 0, v_tactics_2836_);
lean_closure_set(v___f_2847_, 1, v_a_2837_);
lean_closure_set(v___f_2847_, 2, v___x_2846_);
v___x_2848_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
lean_inc_ref(v_collectKinds_2845_);
v___x_2849_ = lean_apply_1(v_collectKinds_2845_, v___x_2848_);
v___x_2850_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_2849_, v_b_2840_, v___f_2847_);
lean_dec_ref(v___x_2849_);
v_as_x27_2839_ = v_tail_2844_;
v_b_2840_ = v___x_2850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_2852_, lean_object* v_a_2853_, lean_object* v___x_2854_, lean_object* v_as_x27_2855_, lean_object* v_b_2856_){
_start:
{
uint8_t v___x_4042__boxed_2857_; lean_object* v_res_2858_; 
v___x_4042__boxed_2857_ = lean_unbox(v___x_2854_);
v_res_2858_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2852_, v_a_2853_, v___x_4042__boxed_2857_, v_as_x27_2855_, v_b_2856_);
lean_dec(v_as_x27_2855_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_2861_, lean_object* v_init_2862_, lean_object* v_x_2863_){
_start:
{
if (lean_obj_tag(v_x_2863_) == 0)
{
lean_object* v_k_2864_; lean_object* v_v_2865_; lean_object* v_l_2866_; lean_object* v_r_2867_; lean_object* v___x_2868_; lean_object* v_a_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v_k_2864_ = lean_ctor_get(v_x_2863_, 1);
lean_inc(v_k_2864_);
v_v_2865_ = lean_ctor_get(v_x_2863_, 2);
lean_inc(v_v_2865_);
v_l_2866_ = lean_ctor_get(v_x_2863_, 3);
lean_inc(v_l_2866_);
v_r_2867_ = lean_ctor_get(v_x_2863_, 4);
lean_inc(v_r_2867_);
lean_dec_ref_known(v_x_2863_, 5);
lean_inc_ref(v_tactics_2861_);
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2861_, v_init_2862_, v_l_2866_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
v___x_2870_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0));
v___x_2871_ = lean_name_eq(v_k_2864_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_dec_ref(v___x_2868_);
lean_inc_ref(v_tactics_2861_);
v___x_2872_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2861_, v_k_2864_, v___x_2871_, v_v_2865_, v_a_2869_);
lean_dec(v_v_2865_);
v_init_2862_ = v___x_2872_;
v_x_2863_ = v_r_2867_;
goto _start;
}
else
{
lean_object* v_a_2874_; 
lean_dec(v_a_2869_);
lean_dec(v_v_2865_);
lean_dec(v_k_2864_);
v_a_2874_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2874_);
lean_dec_ref(v___x_2868_);
v_init_2862_ = v_a_2874_;
v_x_2863_ = v_r_2867_;
goto _start;
}
}
else
{
lean_object* v___x_2876_; 
lean_dec_ref(v_tactics_2861_);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_init_2862_);
return v___x_2876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_2877_, lean_object* v_table_2878_, lean_object* v_firsts_2879_){
_start:
{
lean_object* v___x_2880_; lean_object* v_a_2881_; 
v___x_2880_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_2877_, v_firsts_2879_, v_table_2878_);
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
return v_a_2881_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_2882_, lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
uint8_t v___x_2885_; 
v___x_2885_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_2883_, v_x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_){
_start:
{
uint8_t v_res_2889_; lean_object* v_r_2890_; 
v_res_2889_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_2886_, v_x_2887_, v_x_2888_);
lean_dec(v_x_2888_);
lean_dec_ref(v_x_2887_);
v_r_2890_ = lean_box(v_res_2889_);
return v_r_2890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_2891_, lean_object* v_k_2892_, lean_object* v_t_2893_, lean_object* v_hl_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_2891_, v_k_2892_, v_t_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_2896_, lean_object* v_00_u03b2_2897_, lean_object* v_map_2898_, lean_object* v_init_2899_, lean_object* v_f_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_2898_, v_init_2899_, v_f_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_2902_, lean_object* v_00_u03b2_2903_, lean_object* v_map_2904_, lean_object* v_init_2905_, lean_object* v_f_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_2902_, v_00_u03b2_2903_, v_map_2904_, v_init_2905_, v_f_2906_);
lean_dec_ref(v_map_2904_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_2908_, lean_object* v_a_2909_, uint8_t v___x_2910_, lean_object* v_as_2911_, lean_object* v_as_x27_2912_, lean_object* v_b_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_2908_, v_a_2909_, v___x_2910_, v_as_x27_2912_, v_b_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_2916_, lean_object* v_a_2917_, lean_object* v___x_2918_, lean_object* v_as_2919_, lean_object* v_as_x27_2920_, lean_object* v_b_2921_, lean_object* v_a_2922_){
_start:
{
uint8_t v___x_4122__boxed_2923_; lean_object* v_res_2924_; 
v___x_4122__boxed_2923_ = lean_unbox(v___x_2918_);
v_res_2924_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_2916_, v_a_2917_, v___x_4122__boxed_2923_, v_as_2919_, v_as_x27_2920_, v_b_2921_, v_a_2922_);
lean_dec(v_as_x27_2920_);
lean_dec(v_as_2919_);
return v_res_2924_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_2925_, lean_object* v_x_2926_, size_t v_x_2927_, lean_object* v_x_2928_){
_start:
{
uint8_t v___x_2929_; 
v___x_2929_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_2926_, v_x_2927_, v_x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2930_, lean_object* v_x_2931_, lean_object* v_x_2932_, lean_object* v_x_2933_){
_start:
{
size_t v_x_4131__boxed_2934_; uint8_t v_res_2935_; lean_object* v_r_2936_; 
v_x_4131__boxed_2934_ = lean_unbox_usize(v_x_2932_);
lean_dec(v_x_2932_);
v_res_2935_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_2930_, v_x_2931_, v_x_4131__boxed_2934_, v_x_2933_);
lean_dec(v_x_2933_);
lean_dec_ref(v_x_2931_);
v_r_2936_ = lean_box(v_res_2935_);
return v_r_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_2937_, lean_object* v_f_2938_, lean_object* v_init_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2938_, v_map_2937_, v_init_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_2941_, lean_object* v_00_u03c3_2942_, lean_object* v_00_u03b2_2943_, lean_object* v_map_2944_, lean_object* v_f_2945_, lean_object* v_init_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2945_, v_map_2944_, v_init_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2948_, lean_object* v_keys_2949_, lean_object* v_vals_2950_, lean_object* v_heq_2951_, lean_object* v_i_2952_, lean_object* v_k_2953_){
_start:
{
uint8_t v___x_2954_; 
v___x_2954_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_2949_, v_i_2952_, v_k_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2955_, lean_object* v_keys_2956_, lean_object* v_vals_2957_, lean_object* v_heq_2958_, lean_object* v_i_2959_, lean_object* v_k_2960_){
_start:
{
uint8_t v_res_2961_; lean_object* v_r_2962_; 
v_res_2961_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_2955_, v_keys_2956_, v_vals_2957_, v_heq_2958_, v_i_2959_, v_k_2960_);
lean_dec(v_k_2960_);
lean_dec_ref(v_vals_2957_);
lean_dec_ref(v_keys_2956_);
v_r_2962_ = lean_box(v_res_2961_);
return v_r_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_2963_, lean_object* v_00_u03c3_2964_, lean_object* v_00_u03b1_2965_, lean_object* v_00_u03b2_2966_, lean_object* v_f_2967_, lean_object* v_x_2968_, lean_object* v_x_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_2967_, v_x_2968_, v_x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_2971_, lean_object* v_00_u03b2_2972_, lean_object* v_00_u03c3_2973_, lean_object* v_00_u03c3_2974_, lean_object* v_f_2975_, lean_object* v_as_2976_, size_t v_i_2977_, size_t v_stop_2978_, lean_object* v_b_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_2975_, v_as_2976_, v_i_2977_, v_stop_2978_, v_b_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2981_, lean_object* v_00_u03b2_2982_, lean_object* v_00_u03c3_2983_, lean_object* v_00_u03c3_2984_, lean_object* v_f_2985_, lean_object* v_as_2986_, lean_object* v_i_2987_, lean_object* v_stop_2988_, lean_object* v_b_2989_){
_start:
{
size_t v_i_boxed_2990_; size_t v_stop_boxed_2991_; lean_object* v_res_2992_; 
v_i_boxed_2990_ = lean_unbox_usize(v_i_2987_);
lean_dec(v_i_2987_);
v_stop_boxed_2991_ = lean_unbox_usize(v_stop_2988_);
lean_dec(v_stop_2988_);
v_res_2992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_2981_, v_00_u03b2_2982_, v_00_u03c3_2983_, v_00_u03c3_2984_, v_f_2985_, v_as_2986_, v_i_boxed_2990_, v_stop_boxed_2991_, v_b_2989_);
lean_dec_ref(v_as_2986_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_2993_, lean_object* v_00_u03c3_2994_, lean_object* v_00_u03b1_2995_, lean_object* v_00_u03b2_2996_, lean_object* v_f_2997_, lean_object* v_keys_2998_, lean_object* v_vals_2999_, lean_object* v_heq_3000_, lean_object* v_i_3001_, lean_object* v_acc_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_2997_, v_keys_2998_, v_vals_2999_, v_i_3001_, v_acc_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_3004_, lean_object* v_00_u03c3_3005_, lean_object* v_00_u03b1_3006_, lean_object* v_00_u03b2_3007_, lean_object* v_f_3008_, lean_object* v_keys_3009_, lean_object* v_vals_3010_, lean_object* v_heq_3011_, lean_object* v_i_3012_, lean_object* v_acc_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_3004_, v_00_u03c3_3005_, v_00_u03b1_3006_, v_00_u03b2_3007_, v_f_3008_, v_keys_3009_, v_vals_3010_, v_heq_3011_, v_i_3012_, v_acc_3013_);
lean_dec_ref(v_vals_3010_);
lean_dec_ref(v_keys_3009_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_3015_, lean_object* v_x2_3016_){
_start:
{
lean_object* v_fst_3017_; lean_object* v_snd_3018_; lean_object* v___x_3019_; 
v_fst_3017_ = lean_ctor_get(v_x2_3016_, 0);
lean_inc(v_fst_3017_);
v_snd_3018_ = lean_ctor_get(v_x2_3016_, 1);
lean_inc(v_snd_3018_);
lean_dec_ref(v_x2_3016_);
v___x_3019_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3017_, v_snd_3018_, v_x1_3015_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_3039_, lean_object* v_x1_3040_, lean_object* v_x2_3041_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = lean_array_get_size(v_x2_3041_);
v___x_3044_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_3045_ = lean_nat_dec_lt(v___x_3042_, v___x_3043_);
if (v___x_3045_ == 0)
{
lean_dec_ref(v_x2_3041_);
lean_dec_ref(v___f_3039_);
return v_x1_3040_;
}
else
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_le(v___x_3043_, v___x_3043_);
if (v___x_3046_ == 0)
{
if (v___x_3045_ == 0)
{
lean_dec_ref(v_x2_3041_);
lean_dec_ref(v___f_3039_);
return v_x1_3040_;
}
else
{
size_t v___x_3047_; size_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = ((size_t)0ULL);
v___x_3048_ = lean_usize_of_nat(v___x_3043_);
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3044_, v___f_3039_, v_x2_3041_, v___x_3047_, v___x_3048_, v_x1_3040_);
return v___x_3049_;
}
}
else
{
size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = ((size_t)0ULL);
v___x_3051_ = lean_usize_of_nat(v___x_3043_);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3044_, v___f_3039_, v_x2_3041_, v___x_3050_, v___x_3051_, v_x1_3040_);
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_3056_, lean_object* v___x_3057_, lean_object* v___x_3058_, lean_object* v___x_3059_, lean_object* v___x_3060_, lean_object* v_toPure_3061_, lean_object* v___f_3062_, lean_object* v_env_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v_ext_3065_; lean_object* v_toEnvExtension_3066_; lean_object* v_asyncMode_3067_; lean_object* v___x_3068_; lean_object* v_categories_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3064_ = l_Lean_Parser_parserExtension;
v_ext_3065_ = lean_ctor_get(v___x_3064_, 1);
v_toEnvExtension_3066_ = lean_ctor_get(v_ext_3065_, 0);
v_asyncMode_3067_ = lean_ctor_get(v_toEnvExtension_3066_, 2);
lean_inc_ref(v_env_3063_);
v___x_3068_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3056_, v___x_3064_, v_env_3063_, v_asyncMode_3067_);
v_categories_3069_ = lean_ctor_get(v___x_3068_, 2);
lean_inc_ref(v_categories_3069_);
lean_dec(v___x_3068_);
v___x_3070_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3071_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_3057_, v___x_3058_, v_categories_3069_, v___x_3070_);
lean_dec_ref(v_categories_3069_);
if (lean_obj_tag(v___x_3071_) == 1)
{
lean_object* v_val_3072_; lean_object* v___y_3074_; lean_object* v___x_3081_; lean_object* v_toEnvExtension_3082_; lean_object* v_exportEntriesFn_3083_; lean_object* v_asyncMode_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_importedEntries_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v_exported_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v_val_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_val_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3081_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3082_ = lean_ctor_get(v___x_3081_, 0);
v_exportEntriesFn_3083_ = lean_ctor_get(v___x_3081_, 4);
v_asyncMode_3084_ = lean_ctor_get(v_toEnvExtension_3082_, 2);
v___x_3085_ = lean_box(0);
lean_inc_ref_n(v_env_3063_, 2);
v___x_3086_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3059_, v_toEnvExtension_3082_, v_env_3063_, v_asyncMode_3084_, v___x_3085_);
v_importedEntries_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc_ref(v_importedEntries_3087_);
lean_dec(v___x_3086_);
v___x_3088_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3060_, v___x_3081_, v_env_3063_, v_asyncMode_3084_, v___x_3085_);
lean_inc_ref(v_exportEntriesFn_3083_);
v___x_3089_ = lean_apply_2(v_exportEntriesFn_3083_, v_env_3063_, v___x_3088_);
v_exported_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_exported_3090_);
lean_dec_ref(v___x_3089_);
v___x_3091_ = lean_box(1);
v___x_3092_ = lean_array_push(v_importedEntries_3087_, v_exported_3090_);
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = lean_array_get_size(v___x_3092_);
v___x_3095_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_3096_ = lean_nat_dec_lt(v___x_3093_, v___x_3094_);
if (v___x_3096_ == 0)
{
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___f_3062_);
v___y_3074_ = v___x_3091_;
goto v___jp_3073_;
}
else
{
uint8_t v___x_3097_; 
v___x_3097_ = lean_nat_dec_le(v___x_3094_, v___x_3094_);
if (v___x_3097_ == 0)
{
if (v___x_3096_ == 0)
{
lean_dec_ref(v___x_3092_);
lean_dec_ref(v___f_3062_);
v___y_3074_ = v___x_3091_;
goto v___jp_3073_;
}
else
{
size_t v___x_3098_; size_t v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = lean_usize_of_nat(v___x_3094_);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3095_, v___f_3062_, v___x_3092_, v___x_3098_, v___x_3099_, v___x_3091_);
v___y_3074_ = v___x_3100_;
goto v___jp_3073_;
}
}
else
{
size_t v___x_3101_; size_t v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = ((size_t)0ULL);
v___x_3102_ = lean_usize_of_nat(v___x_3094_);
v___x_3103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3095_, v___f_3062_, v___x_3092_, v___x_3101_, v___x_3102_, v___x_3091_);
v___y_3074_ = v___x_3103_;
goto v___jp_3073_;
}
}
v___jp_3073_:
{
lean_object* v_tables_3075_; lean_object* v_leadingTable_3076_; lean_object* v_trailingTable_3077_; lean_object* v_firstTokens_3078_; lean_object* v_firstTokens_3079_; lean_object* v___x_3080_; 
v_tables_3075_ = lean_ctor_get(v_val_3072_, 2);
v_leadingTable_3076_ = lean_ctor_get(v_tables_3075_, 0);
v_trailingTable_3077_ = lean_ctor_get(v_tables_3075_, 2);
lean_inc(v_trailingTable_3077_);
lean_inc(v_leadingTable_3076_);
lean_inc(v_val_3072_);
v_firstTokens_3078_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3072_, v_leadingTable_3076_, v___y_3074_);
v_firstTokens_3079_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3072_, v_trailingTable_3077_, v_firstTokens_3078_);
v___x_3080_ = lean_apply_2(v_toPure_3061_, lean_box(0), v_firstTokens_3079_);
return v___x_3080_;
}
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec(v___x_3071_);
lean_dec_ref(v_env_3063_);
lean_dec_ref(v___f_3062_);
lean_dec(v___x_3060_);
v___x_3104_ = lean_box(1);
v___x_3105_ = lean_apply_2(v_toPure_3061_, lean_box(0), v___x_3104_);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_3106_, lean_object* v___x_3107_, lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v_toPure_3111_, lean_object* v___f_3112_, lean_object* v_env_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_3106_, v___x_3107_, v___x_3108_, v___x_3109_, v___x_3110_, v_toPure_3111_, v___f_3112_, v_env_3113_);
lean_dec_ref(v___x_3109_);
lean_dec_ref(v___x_3106_);
return v_res_3114_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_box(1);
v___x_3119_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_3122_, lean_object* v_inst_3123_){
_start:
{
lean_object* v_toApplicative_3124_; lean_object* v_toBind_3125_; lean_object* v_getEnv_3126_; lean_object* v_toPure_3127_; lean_object* v___f_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___f_3134_; lean_object* v___x_3135_; 
v_toApplicative_3124_ = lean_ctor_get(v_inst_3122_, 0);
lean_inc_ref(v_toApplicative_3124_);
v_toBind_3125_ = lean_ctor_get(v_inst_3122_, 1);
lean_inc(v_toBind_3125_);
lean_dec_ref(v_inst_3122_);
v_getEnv_3126_ = lean_ctor_get(v_inst_3123_, 0);
lean_inc(v_getEnv_3126_);
lean_dec_ref(v_inst_3123_);
v_toPure_3127_ = lean_ctor_get(v_toApplicative_3124_, 1);
lean_inc(v_toPure_3127_);
lean_dec_ref(v_toApplicative_3124_);
v___f_3128_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_3129_ = lean_box(1);
v___x_3130_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3131_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_3132_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_3133_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_3134_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3134_, 0, v___x_3133_);
lean_closure_set(v___f_3134_, 1, v___x_3131_);
lean_closure_set(v___f_3134_, 2, v___x_3132_);
lean_closure_set(v___f_3134_, 3, v___x_3130_);
lean_closure_set(v___f_3134_, 4, v___x_3129_);
lean_closure_set(v___f_3134_, 5, v_toPure_3127_);
lean_closure_set(v___f_3134_, 6, v___f_3128_);
v___x_3135_ = lean_apply_4(v_toBind_3125_, lean_box(0), lean_box(0), v_getEnv_3126_, v___f_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_3137_, v_inst_3138_);
return v___x_3139_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__0);
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3142_ = lean_box(1);
v___x_3143_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg___closed__4);
v___x_3144_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_3145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v___x_3143_);
lean_ctor_set(v___x_3145_, 2, v___x_3142_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_3147_, lean_object* v___y_3148_, lean_object* v_toPure_3149_, lean_object* v_firsts_3150_, lean_object* v_____do__lift_3151_){
_start:
{
lean_object* v___y_3153_; lean_object* v_val_3164_; 
if (lean_obj_tag(v_____do__lift_3151_) == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2));
lean_inc(v_n_3147_);
v___x_3167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_3166_, v_firsts_3150_, v_n_3147_);
if (lean_obj_tag(v___x_3167_) == 0)
{
uint8_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = 1;
lean_inc(v_n_3147_);
v___x_3169_ = l_Lean_Name_toString(v_n_3147_, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
v___y_3153_ = v___x_3170_;
goto v___jp_3152_;
}
else
{
lean_object* v_val_3171_; 
v_val_3171_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_val_3171_);
lean_dec_ref_known(v___x_3167_, 1);
v_val_3164_ = v_val_3171_;
goto v___jp_3163_;
}
}
else
{
lean_object* v_val_3172_; 
lean_dec(v_firsts_3150_);
v_val_3172_ = lean_ctor_get(v_____do__lift_3151_, 0);
lean_inc(v_val_3172_);
lean_dec_ref_known(v_____do__lift_3151_, 1);
v_val_3164_ = v_val_3172_;
goto v___jp_3163_;
}
v___jp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3154_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_3155_ = l_Lean_Expr_const___override(v_n_3147_, v___y_3148_);
v___x_3156_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_3157_ = lean_box(0);
v___x_3158_ = 0;
v___x_3159_ = l_Lean_MessageData_withExprHover(v___y_3153_, v___x_3155_, v___x_3156_, v___x_3157_, v___x_3157_, v___x_3157_, v___x_3158_);
v___x_3160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3154_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3154_);
v___x_3162_ = lean_apply_2(v_toPure_3149_, lean_box(0), v___x_3161_);
return v___x_3162_;
}
v___jp_3163_:
{
lean_object* v___x_3165_; 
v___x_3165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_val_3164_);
v___y_3153_ = v___x_3165_;
goto v___jp_3152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_3173_, lean_object* v_toPure_3174_, lean_object* v_firsts_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_toBind_3178_, lean_object* v___x_3179_, lean_object* v___x_3180_, lean_object* v___f_3181_, lean_object* v_env_3182_){
_start:
{
lean_object* v___y_3184_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = l_Lean_Environment_constants(v_env_3182_);
lean_inc(v_n_3173_);
v___x_3189_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_3179_, v___x_3180_, v___x_3188_, v_n_3173_);
lean_dec_ref(v___x_3188_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v___x_3190_; 
lean_dec_ref(v___f_3181_);
v___x_3190_ = lean_box(0);
v___y_3184_ = v___x_3190_;
goto v___jp_3183_;
}
else
{
lean_object* v_val_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_val_3191_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_val_3191_);
lean_dec_ref_known(v___x_3189_, 1);
v___x_3192_ = l_Lean_ConstantInfo_levelParams(v_val_3191_);
lean_dec(v_val_3191_);
v___x_3193_ = lean_box(0);
v___x_3194_ = l_List_mapTR_loop___redArg(v___f_3181_, v___x_3192_, v___x_3193_);
v___y_3184_ = v___x_3194_;
goto v___jp_3183_;
}
v___jp_3183_:
{
lean_object* v___f_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_inc(v_n_3173_);
v___f_3185_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_3185_, 0, v_n_3173_);
lean_closure_set(v___f_3185_, 1, v___y_3184_);
lean_closure_set(v___f_3185_, 2, v_toPure_3174_);
lean_closure_set(v___f_3185_, 3, v_firsts_3175_);
v___x_3186_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_3176_, v_inst_3177_, v_n_3173_);
v___x_3187_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v___x_3186_, v___f_3185_);
return v___x_3187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_firsts_3198_, lean_object* v_n_3199_){
_start:
{
lean_object* v_toApplicative_3200_; lean_object* v_toBind_3201_; lean_object* v_getEnv_3202_; lean_object* v_toPure_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; 
v_toApplicative_3200_ = lean_ctor_get(v_inst_3196_, 0);
v_toBind_3201_ = lean_ctor_get(v_inst_3196_, 1);
lean_inc_n(v_toBind_3201_, 2);
v_getEnv_3202_ = lean_ctor_get(v_inst_3197_, 0);
lean_inc(v_getEnv_3202_);
v_toPure_3203_ = lean_ctor_get(v_toApplicative_3200_, 1);
lean_inc(v_toPure_3203_);
v___f_3204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_3205_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_3206_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_3207_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_3207_, 0, v_n_3199_);
lean_closure_set(v___f_3207_, 1, v_toPure_3203_);
lean_closure_set(v___f_3207_, 2, v_firsts_3198_);
lean_closure_set(v___f_3207_, 3, v_inst_3196_);
lean_closure_set(v___f_3207_, 4, v_inst_3197_);
lean_closure_set(v___f_3207_, 5, v_toBind_3201_);
lean_closure_set(v___f_3207_, 6, v___x_3205_);
lean_closure_set(v___f_3207_, 7, v___x_3206_);
lean_closure_set(v___f_3207_, 8, v___f_3204_);
v___x_3208_ = lean_apply_4(v_toBind_3201_, lean_box(0), lean_box(0), v_getEnv_3202_, v___f_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_firsts_3212_, lean_object* v_n_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_3210_, v_inst_3211_, v_firsts_3212_, v_n_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg(){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___closed__0));
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg___boxed(lean_object* v___dummy_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v_res_3220_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0(void){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___redArg();
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_3222_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_3224_);
lean_dec_ref(v_s_3224_);
return v_res_3225_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_3226_, lean_object* v_x1_3227_, lean_object* v_x2_3228_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3229_ = l_Lean_Name_toString(v_x1_3227_, v___x_3226_);
v___x_3230_ = l_Lean_Name_toString(v_x2_3228_, v___x_3226_);
v___x_3231_ = lean_string_dec_lt(v___x_3229_, v___x_3230_);
lean_dec_ref(v___x_3230_);
lean_dec_ref(v___x_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_3232_, lean_object* v_x1_3233_, lean_object* v_x2_3234_){
_start:
{
uint8_t v___x_16939__boxed_3235_; uint8_t v_res_3236_; lean_object* v_r_3237_; 
v___x_16939__boxed_3235_ = lean_unbox(v___x_3232_);
v_res_3236_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_16939__boxed_3235_, v_x1_3233_, v_x2_3234_);
v_r_3237_ = lean_box(v_res_3236_);
return v_r_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_3238_, lean_object* v_pivot_3239_, lean_object* v_as_3240_, lean_object* v_i_3241_, lean_object* v_k_3242_){
_start:
{
uint8_t v___x_3243_; 
v___x_3243_ = lean_nat_dec_lt(v_k_3242_, v_hi_3238_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
lean_dec(v_k_3242_);
lean_dec(v_pivot_3239_);
v___x_3244_ = lean_array_fswap(v_as_3240_, v_i_3241_, v_hi_3238_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v_i_3241_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
return v___x_3245_;
}
else
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3246_ = lean_array_fget_borrowed(v_as_3240_, v_k_3242_);
lean_inc(v___x_3246_);
v___x_3247_ = l_Lean_Name_toString(v___x_3246_, v___x_3243_);
lean_inc(v_pivot_3239_);
v___x_3248_ = l_Lean_Name_toString(v_pivot_3239_, v___x_3243_);
v___x_3249_ = lean_string_dec_lt(v___x_3247_, v___x_3248_);
lean_dec_ref(v___x_3248_);
lean_dec_ref(v___x_3247_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_unsigned_to_nat(1u);
v___x_3251_ = lean_nat_add(v_k_3242_, v___x_3250_);
lean_dec(v_k_3242_);
v_k_3242_ = v___x_3251_;
goto _start;
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3253_ = lean_array_fswap(v_as_3240_, v_i_3241_, v_k_3242_);
v___x_3254_ = lean_unsigned_to_nat(1u);
v___x_3255_ = lean_nat_add(v_i_3241_, v___x_3254_);
lean_dec(v_i_3241_);
v___x_3256_ = lean_nat_add(v_k_3242_, v___x_3254_);
lean_dec(v_k_3242_);
v_as_3240_ = v___x_3253_;
v_i_3241_ = v___x_3255_;
v_k_3242_ = v___x_3256_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_3258_, lean_object* v_pivot_3259_, lean_object* v_as_3260_, lean_object* v_i_3261_, lean_object* v_k_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_3258_, v_pivot_3259_, v_as_3260_, v_i_3261_, v_k_3262_);
lean_dec(v_hi_3258_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_3264_, lean_object* v_as_3265_, lean_object* v_lo_3266_, lean_object* v_hi_3267_){
_start:
{
lean_object* v___y_3269_; uint8_t v___x_3279_; 
v___x_3279_ = lean_nat_dec_lt(v_lo_3266_, v_hi_3267_);
if (v___x_3279_ == 0)
{
lean_dec(v_lo_3266_);
return v_as_3265_;
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v_mid_3282_; lean_object* v___y_3284_; lean_object* v___y_3290_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v___x_3280_ = lean_nat_add(v_lo_3266_, v_hi_3267_);
v___x_3281_ = lean_unsigned_to_nat(1u);
v_mid_3282_ = lean_nat_shiftr(v___x_3280_, v___x_3281_);
lean_dec(v___x_3280_);
v___x_3295_ = lean_array_fget_borrowed(v_as_3265_, v_mid_3282_);
v___x_3296_ = lean_array_fget_borrowed(v_as_3265_, v_lo_3266_);
lean_inc(v___x_3296_);
lean_inc(v___x_3295_);
v___x_3297_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_3279_, v___x_3295_, v___x_3296_);
if (v___x_3297_ == 0)
{
v___y_3290_ = v_as_3265_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_array_fswap(v_as_3265_, v_lo_3266_, v_mid_3282_);
v___y_3290_ = v___x_3298_;
goto v___jp_3289_;
}
v___jp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3285_ = lean_array_fget_borrowed(v___y_3284_, v_mid_3282_);
v___x_3286_ = lean_array_fget_borrowed(v___y_3284_, v_hi_3267_);
lean_inc(v___x_3286_);
lean_inc(v___x_3285_);
v___x_3287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_3279_, v___x_3285_, v___x_3286_);
if (v___x_3287_ == 0)
{
lean_dec(v_mid_3282_);
v___y_3269_ = v___y_3284_;
goto v___jp_3268_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_array_fswap(v___y_3284_, v_mid_3282_, v_hi_3267_);
lean_dec(v_mid_3282_);
v___y_3269_ = v___x_3288_;
goto v___jp_3268_;
}
}
v___jp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3291_ = lean_array_fget_borrowed(v___y_3290_, v_hi_3267_);
v___x_3292_ = lean_array_fget_borrowed(v___y_3290_, v_lo_3266_);
lean_inc(v___x_3292_);
lean_inc(v___x_3291_);
v___x_3293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_3279_, v___x_3291_, v___x_3292_);
if (v___x_3293_ == 0)
{
v___y_3284_ = v___y_3290_;
goto v___jp_3283_;
}
else
{
lean_object* v___x_3294_; 
v___x_3294_ = lean_array_fswap(v___y_3290_, v_lo_3266_, v_hi_3267_);
v___y_3284_ = v___x_3294_;
goto v___jp_3283_;
}
}
}
v___jp_3268_:
{
lean_object* v_pivot_3270_; lean_object* v___x_3271_; lean_object* v_fst_3272_; lean_object* v_snd_3273_; uint8_t v___x_3274_; 
v_pivot_3270_ = lean_array_fget(v___y_3269_, v_hi_3267_);
lean_inc_n(v_lo_3266_, 2);
v___x_3271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_3267_, v_pivot_3270_, v___y_3269_, v_lo_3266_, v_lo_3266_);
v_fst_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_fst_3272_);
v_snd_3273_ = lean_ctor_get(v___x_3271_, 1);
lean_inc(v_snd_3273_);
lean_dec_ref(v___x_3271_);
v___x_3274_ = lean_nat_dec_le(v_hi_3267_, v_fst_3272_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_3264_, v_snd_3273_, v_lo_3266_, v_fst_3272_);
v___x_3276_ = lean_unsigned_to_nat(1u);
v___x_3277_ = lean_nat_add(v_fst_3272_, v___x_3276_);
lean_dec(v_fst_3272_);
v_as_3265_ = v___x_3275_;
v_lo_3266_ = v___x_3277_;
goto _start;
}
else
{
lean_dec(v_fst_3272_);
lean_dec(v_lo_3266_);
return v_snd_3273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_3299_, lean_object* v_as_3300_, lean_object* v_lo_3301_, lean_object* v_hi_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_3299_, v_as_3300_, v_lo_3301_, v_hi_3302_);
lean_dec(v_hi_3302_);
lean_dec(v_n_3299_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_3304_, lean_object* v_x_3305_){
_start:
{
if (lean_obj_tag(v_x_3305_) == 0)
{
lean_object* v_k_3306_; lean_object* v_l_3307_; lean_object* v_r_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_k_3306_ = lean_ctor_get(v_x_3305_, 1);
lean_inc(v_k_3306_);
v_l_3307_ = lean_ctor_get(v_x_3305_, 3);
lean_inc(v_l_3307_);
v_r_3308_ = lean_ctor_get(v_x_3305_, 4);
lean_inc(v_r_3308_);
lean_dec_ref_known(v_x_3305_, 5);
v___x_3309_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_3304_, v_l_3307_);
v___x_3310_ = lean_array_push(v___x_3309_, v_k_3306_);
v_init_3304_ = v___x_3310_;
v_x_3305_ = v_r_3308_;
goto _start;
}
else
{
return v_init_3304_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
if (lean_obj_tag(v_a_3312_) == 0)
{
lean_object* v___x_3314_; 
v___x_3314_ = l_List_reverse___redArg(v_a_3313_);
return v___x_3314_;
}
else
{
lean_object* v_head_3315_; lean_object* v_tail_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3325_; 
v_head_3315_ = lean_ctor_get(v_a_3312_, 0);
v_tail_3316_ = lean_ctor_get(v_a_3312_, 1);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_a_3312_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3318_ = v_a_3312_;
v_isShared_3319_ = v_isSharedCheck_3325_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_tail_3316_);
lean_inc(v_head_3315_);
lean_dec(v_a_3312_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3325_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3320_ = l_Lean_Level_param___override(v_head_3315_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 1, v_a_3313_);
lean_ctor_set(v___x_3318_, 0, v___x_3320_);
v___x_3322_ = v___x_3318_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3320_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_a_3313_);
v___x_3322_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
v_a_3312_ = v_tail_3316_;
v_a_3313_ = v___x_3322_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_3326_, lean_object* v_x2_3327_){
_start:
{
lean_object* v_fst_3328_; lean_object* v_fst_3329_; uint8_t v___x_3330_; 
v_fst_3328_ = lean_ctor_get(v_x1_3326_, 0);
v_fst_3329_ = lean_ctor_get(v_x2_3327_, 0);
v___x_3330_ = l_Lean_Name_quickLt(v_fst_3328_, v_fst_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_3331_, lean_object* v_x2_3332_){
_start:
{
uint8_t v_res_3333_; lean_object* v_r_3334_; 
v_res_3333_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_3331_, v_x2_3332_);
lean_dec_ref(v_x2_3332_);
lean_dec_ref(v_x1_3331_);
v_r_3334_ = lean_box(v_res_3333_);
return v_r_3334_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_3335_, lean_object* v_k_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v_m_3341_; lean_object* v_a_3342_; uint8_t v___x_3343_; 
v___x_3339_ = lean_nat_add(v_x_3337_, v_x_3338_);
v___x_3340_ = lean_unsigned_to_nat(1u);
v_m_3341_ = lean_nat_shiftr(v___x_3339_, v___x_3340_);
lean_dec(v___x_3339_);
v_a_3342_ = lean_array_fget_borrowed(v_as_3335_, v_m_3341_);
v___x_3343_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_3342_, v_k_3336_);
if (v___x_3343_ == 0)
{
uint8_t v___x_3344_; 
lean_dec(v_x_3338_);
v___x_3344_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_3336_, v_a_3342_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_dec(v_m_3341_);
lean_dec(v_x_3337_);
lean_inc(v_a_3342_);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v_a_3342_);
return v___x_3345_;
}
else
{
lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; uint8_t v___y_3350_; 
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3347_ = lean_nat_dec_eq(v_m_3341_, v___x_3346_);
v___x_3348_ = lean_nat_sub(v_m_3341_, v___x_3340_);
lean_dec(v_m_3341_);
if (v___x_3347_ == 0)
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_nat_dec_lt(v___x_3348_, v_x_3337_);
v___y_3350_ = v___x_3353_;
goto v___jp_3349_;
}
else
{
v___y_3350_ = v___x_3347_;
goto v___jp_3349_;
}
v___jp_3349_:
{
if (v___y_3350_ == 0)
{
v_x_3338_ = v___x_3348_;
goto _start;
}
else
{
lean_object* v___x_3352_; 
lean_dec(v___x_3348_);
lean_dec(v_x_3337_);
v___x_3352_ = lean_box(0);
return v___x_3352_;
}
}
}
}
else
{
lean_object* v___x_3354_; uint8_t v___x_3355_; 
lean_dec(v_x_3337_);
v___x_3354_ = lean_nat_add(v_m_3341_, v___x_3340_);
lean_dec(v_m_3341_);
v___x_3355_ = lean_nat_dec_le(v___x_3354_, v_x_3338_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
lean_dec(v___x_3354_);
lean_dec(v_x_3338_);
v___x_3356_ = lean_box(0);
return v___x_3356_;
}
else
{
v_x_3337_ = v___x_3354_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_3358_, lean_object* v_k_3359_, lean_object* v_x_3360_, lean_object* v_x_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3358_, v_k_3359_, v_x_3360_, v_x_3361_);
lean_dec_ref(v_k_3359_);
lean_dec_ref(v_as_3358_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v_env_3371_; lean_object* v___x_3372_; 
v___x_3366_ = lean_box(1);
v___x_3367_ = lean_st_ref_get(v___y_3364_);
v_env_3371_ = lean_ctor_get(v___x_3367_, 0);
lean_inc_ref(v_env_3371_);
lean_dec(v___x_3367_);
v___x_3372_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3371_, v_tac_3363_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v___x_3373_; lean_object* v_toEnvExtension_3374_; lean_object* v_asyncMode_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3373_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3374_ = lean_ctor_get(v___x_3373_, 0);
v_asyncMode_3375_ = lean_ctor_get(v_toEnvExtension_3374_, 2);
v___x_3376_ = lean_box(0);
v___x_3377_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3366_, v___x_3373_, v_env_3371_, v_asyncMode_3375_, v___x_3376_);
v___x_3378_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3377_, v_tac_3363_);
lean_dec(v_tac_3363_);
lean_dec(v___x_3377_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
else
{
lean_object* v_val_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3408_; 
v_val_3380_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3382_ = v___x_3372_;
v_isShared_3383_ = v_isSharedCheck_3408_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_val_3380_);
lean_dec(v___x_3372_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3408_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3384_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_3385_ = 0;
v___x_3386_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3366_, v___x_3384_, v_env_3371_, v_val_3380_, v___x_3385_);
lean_dec(v_val_3380_);
lean_dec_ref(v_env_3371_);
v___x_3387_ = lean_unsigned_to_nat(0u);
v___x_3388_ = lean_array_get_size(v___x_3386_);
v___x_3389_ = lean_nat_dec_lt(v___x_3387_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_dec_ref(v___x_3386_);
lean_del_object(v___x_3382_);
lean_dec(v_tac_3363_);
goto v___jp_3368_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3390_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_nat_sub(v___x_3388_, v___x_3390_);
v___x_3392_ = lean_nat_dec_le(v___x_3387_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_dec(v___x_3391_);
lean_dec_ref(v___x_3386_);
lean_del_object(v___x_3382_);
lean_dec(v_tac_3363_);
goto v___jp_3368_;
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7));
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v_tac_3363_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
v___x_3395_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_3386_, v___x_3394_, v___x_3387_, v___x_3391_);
lean_dec_ref_known(v___x_3394_, 2);
lean_dec_ref(v___x_3386_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_del_object(v___x_3382_);
goto v___jp_3368_;
}
else
{
lean_object* v_val_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3407_; 
v_val_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3407_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_val_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3407_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_snd_3400_; lean_object* v___x_3402_; 
v_snd_3400_ = lean_ctor_get(v_val_3396_, 1);
lean_inc(v_snd_3400_);
lean_dec(v_val_3396_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v_snd_3400_);
v___x_3402_ = v___x_3398_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_snd_3400_);
v___x_3402_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3404_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set_tag(v___x_3382_, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3402_);
v___x_3404_ = v___x_3382_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
}
}
}
v___jp_3368_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = lean_box(0);
v___x_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
return v___x_3370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3409_, v___y_3410_);
lean_dec(v___y_3410_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_3413_, lean_object* v_k_3414_){
_start:
{
if (lean_obj_tag(v_t_3413_) == 0)
{
lean_object* v_k_3415_; lean_object* v_v_3416_; lean_object* v_l_3417_; lean_object* v_r_3418_; uint8_t v___x_3419_; 
v_k_3415_ = lean_ctor_get(v_t_3413_, 1);
v_v_3416_ = lean_ctor_get(v_t_3413_, 2);
v_l_3417_ = lean_ctor_get(v_t_3413_, 3);
v_r_3418_ = lean_ctor_get(v_t_3413_, 4);
v___x_3419_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3414_, v_k_3415_);
switch(v___x_3419_)
{
case 0:
{
v_t_3413_ = v_l_3417_;
goto _start;
}
case 1:
{
lean_object* v___x_3421_; 
lean_inc(v_v_3416_);
v___x_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_v_3416_);
return v___x_3421_;
}
default: 
{
v_t_3413_ = v_r_3418_;
goto _start;
}
}
}
else
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_box(0);
return v___x_3423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_3424_, lean_object* v_k_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_3424_, v_k_3425_);
lean_dec(v_k_3425_);
lean_dec(v_t_3424_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_3427_, lean_object* v_x_3428_){
_start:
{
if (lean_obj_tag(v_x_3428_) == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_box(0);
return v___x_3429_;
}
else
{
lean_object* v_key_3430_; lean_object* v_value_3431_; lean_object* v_tail_3432_; uint8_t v___x_3433_; 
v_key_3430_ = lean_ctor_get(v_x_3428_, 0);
v_value_3431_ = lean_ctor_get(v_x_3428_, 1);
v_tail_3432_ = lean_ctor_get(v_x_3428_, 2);
v___x_3433_ = lean_name_eq(v_key_3430_, v_a_3427_);
if (v___x_3433_ == 0)
{
v_x_3428_ = v_tail_3432_;
goto _start;
}
else
{
lean_object* v___x_3435_; 
lean_inc(v_value_3431_);
v___x_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3435_, 0, v_value_3431_);
return v___x_3435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_3436_, lean_object* v_x_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3436_, v_x_3437_);
lean_dec(v_x_3437_);
lean_dec(v_a_3436_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v_buckets_3441_; lean_object* v___x_3442_; uint64_t v___y_3444_; 
v_buckets_3441_ = lean_ctor_get(v_m_3439_, 1);
v___x_3442_ = lean_array_get_size(v_buckets_3441_);
if (lean_obj_tag(v_a_3440_) == 0)
{
uint64_t v___x_3458_; 
v___x_3458_ = 1723ULL;
v___y_3444_ = v___x_3458_;
goto v___jp_3443_;
}
else
{
uint64_t v_hash_3459_; 
v_hash_3459_ = lean_ctor_get_uint64(v_a_3440_, sizeof(void*)*2);
v___y_3444_ = v_hash_3459_;
goto v___jp_3443_;
}
v___jp_3443_:
{
uint64_t v___x_3445_; uint64_t v___x_3446_; uint64_t v_fold_3447_; uint64_t v___x_3448_; uint64_t v___x_3449_; uint64_t v___x_3450_; size_t v___x_3451_; size_t v___x_3452_; size_t v___x_3453_; size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3445_ = 32ULL;
v___x_3446_ = lean_uint64_shift_right(v___y_3444_, v___x_3445_);
v_fold_3447_ = lean_uint64_xor(v___y_3444_, v___x_3446_);
v___x_3448_ = 16ULL;
v___x_3449_ = lean_uint64_shift_right(v_fold_3447_, v___x_3448_);
v___x_3450_ = lean_uint64_xor(v_fold_3447_, v___x_3449_);
v___x_3451_ = lean_uint64_to_usize(v___x_3450_);
v___x_3452_ = lean_usize_of_nat(v___x_3442_);
v___x_3453_ = ((size_t)1ULL);
v___x_3454_ = lean_usize_sub(v___x_3452_, v___x_3453_);
v___x_3455_ = lean_usize_land(v___x_3451_, v___x_3454_);
v___x_3456_ = lean_array_uget_borrowed(v_buckets_3441_, v___x_3455_);
v___x_3457_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3440_, v___x_3456_);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3460_, v_a_3461_);
lean_dec(v_a_3461_);
lean_dec_ref(v_m_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_3463_, lean_object* v_vals_3464_, lean_object* v_i_3465_, lean_object* v_k_3466_){
_start:
{
lean_object* v___x_3467_; uint8_t v___x_3468_; 
v___x_3467_ = lean_array_get_size(v_keys_3463_);
v___x_3468_ = lean_nat_dec_lt(v_i_3465_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; 
lean_dec(v_i_3465_);
v___x_3469_ = lean_box(0);
return v___x_3469_;
}
else
{
lean_object* v_k_x27_3470_; uint8_t v___x_3471_; 
v_k_x27_3470_ = lean_array_fget_borrowed(v_keys_3463_, v_i_3465_);
v___x_3471_ = lean_name_eq(v_k_3466_, v_k_x27_3470_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_add(v_i_3465_, v___x_3472_);
lean_dec(v_i_3465_);
v_i_3465_ = v___x_3473_;
goto _start;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = lean_array_fget_borrowed(v_vals_3464_, v_i_3465_);
lean_dec(v_i_3465_);
lean_inc(v___x_3475_);
v___x_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_3477_, lean_object* v_vals_3478_, lean_object* v_i_3479_, lean_object* v_k_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3477_, v_vals_3478_, v_i_3479_, v_k_3480_);
lean_dec(v_k_3480_);
lean_dec_ref(v_vals_3478_);
lean_dec_ref(v_keys_3477_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_3482_, size_t v_x_3483_, lean_object* v_x_3484_){
_start:
{
if (lean_obj_tag(v_x_3482_) == 0)
{
lean_object* v_es_3485_; lean_object* v___x_3486_; size_t v___x_3487_; size_t v___x_3488_; lean_object* v_j_3489_; lean_object* v___x_3490_; 
v_es_3485_ = lean_ctor_get(v_x_3482_, 0);
v___x_3486_ = lean_box(2);
v___x_3487_ = ((size_t)31ULL);
v___x_3488_ = lean_usize_land(v_x_3483_, v___x_3487_);
v_j_3489_ = lean_usize_to_nat(v___x_3488_);
v___x_3490_ = lean_array_get_borrowed(v___x_3486_, v_es_3485_, v_j_3489_);
lean_dec(v_j_3489_);
switch(lean_obj_tag(v___x_3490_))
{
case 0:
{
lean_object* v_key_3491_; lean_object* v_val_3492_; uint8_t v___x_3493_; 
v_key_3491_ = lean_ctor_get(v___x_3490_, 0);
v_val_3492_ = lean_ctor_get(v___x_3490_, 1);
v___x_3493_ = lean_name_eq(v_x_3484_, v_key_3491_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
v___x_3494_ = lean_box(0);
return v___x_3494_;
}
else
{
lean_object* v___x_3495_; 
lean_inc(v_val_3492_);
v___x_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_val_3492_);
return v___x_3495_;
}
}
case 1:
{
lean_object* v_node_3496_; size_t v___x_3497_; size_t v___x_3498_; 
v_node_3496_ = lean_ctor_get(v___x_3490_, 0);
v___x_3497_ = ((size_t)5ULL);
v___x_3498_ = lean_usize_shift_right(v_x_3483_, v___x_3497_);
v_x_3482_ = v_node_3496_;
v_x_3483_ = v___x_3498_;
goto _start;
}
default: 
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_box(0);
return v___x_3500_;
}
}
}
else
{
lean_object* v_ks_3501_; lean_object* v_vs_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v_ks_3501_ = lean_ctor_get(v_x_3482_, 0);
v_vs_3502_ = lean_ctor_get(v_x_3482_, 1);
v___x_3503_ = lean_unsigned_to_nat(0u);
v___x_3504_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_3501_, v_vs_3502_, v___x_3503_, v_x_3484_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_3505_, lean_object* v_x_3506_, lean_object* v_x_3507_){
_start:
{
size_t v_x_17312__boxed_3508_; lean_object* v_res_3509_; 
v_x_17312__boxed_3508_ = lean_unbox_usize(v_x_3506_);
lean_dec(v_x_3506_);
v_res_3509_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3505_, v_x_17312__boxed_3508_, v_x_3507_);
lean_dec(v_x_3507_);
lean_dec_ref(v_x_3505_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_3510_, lean_object* v_x_3511_){
_start:
{
uint64_t v___y_3513_; 
if (lean_obj_tag(v_x_3511_) == 0)
{
uint64_t v___x_3516_; 
v___x_3516_ = 1723ULL;
v___y_3513_ = v___x_3516_;
goto v___jp_3512_;
}
else
{
uint64_t v_hash_3517_; 
v_hash_3517_ = lean_ctor_get_uint64(v_x_3511_, sizeof(void*)*2);
v___y_3513_ = v_hash_3517_;
goto v___jp_3512_;
}
v___jp_3512_:
{
size_t v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = lean_uint64_to_usize(v___y_3513_);
v___x_3515_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3510_, v___x_3514_, v_x_3511_);
return v___x_3515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_3518_, lean_object* v_x_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3518_, v_x_3519_);
lean_dec(v_x_3519_);
lean_dec_ref(v_x_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_3521_, lean_object* v_x_3522_){
_start:
{
uint8_t v_stage_u2081_3523_; 
v_stage_u2081_3523_ = lean_ctor_get_uint8(v_x_3521_, sizeof(void*)*2);
if (v_stage_u2081_3523_ == 0)
{
lean_object* v_map_u2081_3524_; lean_object* v_map_u2082_3525_; lean_object* v___x_3526_; 
v_map_u2081_3524_ = lean_ctor_get(v_x_3521_, 0);
v_map_u2082_3525_ = lean_ctor_get(v_x_3521_, 1);
v___x_3526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3524_, v_x_3522_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_3525_, v_x_3522_);
return v___x_3527_;
}
else
{
return v___x_3526_;
}
}
else
{
lean_object* v_map_u2081_3528_; lean_object* v___x_3529_; 
v_map_u2081_3528_ = lean_ctor_get(v_x_3521_, 0);
v___x_3529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_3528_, v_x_3522_);
return v___x_3529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_3530_, lean_object* v_x_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_3530_, v_x_3531_);
lean_dec(v_x_3531_);
lean_dec_ref(v_x_3530_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_3533_, lean_object* v_n_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3553_; lean_object* v_val_3554_; lean_object* v___x_3556_; lean_object* v___y_3558_; lean_object* v_env_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3556_ = lean_st_ref_get(v___y_3536_);
v_env_3573_ = lean_ctor_get(v___x_3556_, 0);
lean_inc_ref(v_env_3573_);
lean_dec(v___x_3556_);
v___x_3574_ = l_Lean_Environment_constants(v_env_3573_);
v___x_3575_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_3574_, v_n_3534_);
lean_dec_ref(v___x_3574_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_box(0);
v___y_3558_ = v___x_3576_;
goto v___jp_3557_;
}
else
{
lean_object* v_val_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_val_3577_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_val_3577_);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3578_ = l_Lean_ConstantInfo_levelParams(v_val_3577_);
lean_dec(v_val_3577_);
v___x_3579_ = lean_box(0);
v___x_3580_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_3578_, v___x_3579_);
v___y_3558_ = v___x_3580_;
goto v___jp_3557_;
}
v___jp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3541_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
v___x_3542_ = l_Lean_Expr_const___override(v_n_3534_, v___y_3539_);
v___x_3543_ = lean_unsigned_to_nat(32u);
v___x_3544_ = lean_mk_empty_array_with_capacity(v___x_3543_);
lean_dec_ref(v___x_3544_);
v___x_3545_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_3546_ = lean_box(0);
v___x_3547_ = 0;
v___x_3548_ = l_Lean_MessageData_withExprHover(v___y_3540_, v___x_3542_, v___x_3545_, v___x_3546_, v___x_3546_, v___x_3546_, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3541_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v___x_3541_);
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
v___jp_3552_:
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_val_3554_);
v___y_3539_ = v___y_3553_;
v___y_3540_ = v___x_3555_;
goto v___jp_3538_;
}
v___jp_3557_:
{
lean_object* v___x_3559_; lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3572_; 
lean_inc(v_n_3534_);
v___x_3559_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_3534_, v___y_3536_);
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3562_ = v___x_3559_;
v_isShared_3563_ = v_isSharedCheck_3572_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3572_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
if (lean_obj_tag(v_a_3560_) == 0)
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_3533_, v_n_3534_);
if (lean_obj_tag(v___x_3564_) == 0)
{
uint8_t v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3565_ = 1;
lean_inc(v_n_3534_);
v___x_3566_ = l_Lean_Name_toString(v_n_3534_, v___x_3565_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set_tag(v___x_3562_, 3);
lean_ctor_set(v___x_3562_, 0, v___x_3566_);
v___x_3568_ = v___x_3562_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
v___y_3539_ = v___y_3558_;
v___y_3540_ = v___x_3568_;
goto v___jp_3538_;
}
}
else
{
lean_object* v_val_3570_; 
lean_del_object(v___x_3562_);
v_val_3570_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_val_3570_);
lean_dec_ref_known(v___x_3564_, 1);
v___y_3553_ = v___y_3558_;
v_val_3554_ = v_val_3570_;
goto v___jp_3552_;
}
}
else
{
lean_object* v_val_3571_; 
lean_del_object(v___x_3562_);
v_val_3571_ = lean_ctor_get(v_a_3560_, 0);
lean_inc(v_val_3571_);
lean_dec_ref_known(v_a_3560_, 1);
v___y_3553_ = v___y_3558_;
v_val_3554_ = v_val_3571_;
goto v___jp_3552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_3581_, lean_object* v_n_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_3581_, v_n_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v_firsts_3581_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = l_List_reverse___redArg(v_x_3589_);
v___x_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
return v___x_3594_;
}
else
{
lean_object* v_head_3595_; lean_object* v_tail_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3614_; 
v_head_3595_ = lean_ctor_get(v_x_3588_, 0);
v_tail_3596_ = lean_ctor_get(v_x_3588_, 1);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_x_3588_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3598_ = v_x_3588_;
v_isShared_3599_ = v_isSharedCheck_3614_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_tail_3596_);
lean_inc(v_head_3595_);
lean_dec(v_x_3588_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3614_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; 
v___x_3600_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_3587_, v_head_3595_, v___y_3590_, v___y_3591_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v_x_3589_);
lean_ctor_set(v___x_3598_, 0, v_a_3601_);
v___x_3603_ = v___x_3598_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3601_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_x_3589_);
v___x_3603_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
v_x_3588_ = v_tail_3596_;
v_x_3589_ = v___x_3603_;
goto _start;
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_del_object(v___x_3598_);
lean_dec(v_tail_3596_);
lean_dec(v_x_3589_);
v_a_3606_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3600_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3600_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3615_, v_x_3616_, v_x_3617_, v___y_3618_, v___y_3619_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v_a_3615_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_3622_, lean_object* v___x_3623_, lean_object* v___x_3624_, lean_object* v_a_3625_, lean_object* v_b_3626_){
_start:
{
lean_object* v_it_3628_; lean_object* v_startInclusive_3629_; lean_object* v_endExclusive_3630_; 
if (lean_obj_tag(v_a_3625_) == 0)
{
lean_object* v_currPos_3635_; lean_object* v_searcher_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3659_; 
v_currPos_3635_ = lean_ctor_get(v_a_3625_, 0);
v_searcher_3636_ = lean_ctor_get(v_a_3625_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3625_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3638_ = v_a_3625_;
v_isShared_3639_ = v_isSharedCheck_3659_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_searcher_3636_);
lean_inc(v_currPos_3635_);
lean_dec(v_a_3625_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3659_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
uint8_t v_decide_3640_; 
v_decide_3640_ = lean_nat_dec_eq(v_searcher_3636_, v___x_3624_);
if (v_decide_3640_ == 0)
{
uint32_t v___x_3641_; uint32_t v___x_3642_; uint8_t v___x_3643_; 
v___x_3641_ = 10;
v___x_3642_ = lean_string_utf8_get_fast(v_val_3622_, v_searcher_3636_);
v___x_3643_ = lean_uint32_dec_eq(v___x_3642_, v___x_3641_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3644_ = lean_string_utf8_next_fast(v_val_3622_, v_searcher_3636_);
lean_dec(v_searcher_3636_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 1, v___x_3644_);
v___x_3646_ = v___x_3638_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_currPos_3635_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
v_a_3625_ = v___x_3646_;
goto _start;
}
}
else
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v_slice_3652_; lean_object* v_nextIt_3654_; 
v___x_3649_ = lean_string_utf8_next_fast(v_val_3622_, v_searcher_3636_);
v___x_3650_ = lean_nat_sub(v___x_3649_, v_searcher_3636_);
v___x_3651_ = lean_nat_add(v_searcher_3636_, v___x_3650_);
lean_dec(v___x_3650_);
v_slice_3652_ = l_String_Slice_subslice_x21(v___x_3623_, v_currPos_3635_, v_searcher_3636_);
lean_inc(v___x_3651_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 1, v___x_3651_);
lean_ctor_set(v___x_3638_, 0, v___x_3651_);
v_nextIt_3654_ = v___x_3638_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v___x_3651_);
v_nextIt_3654_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v_startInclusive_3655_; lean_object* v_endExclusive_3656_; 
v_startInclusive_3655_ = lean_ctor_get(v_slice_3652_, 0);
lean_inc(v_startInclusive_3655_);
v_endExclusive_3656_ = lean_ctor_get(v_slice_3652_, 1);
lean_inc(v_endExclusive_3656_);
lean_dec_ref(v_slice_3652_);
v_it_3628_ = v_nextIt_3654_;
v_startInclusive_3629_ = v_startInclusive_3655_;
v_endExclusive_3630_ = v_endExclusive_3656_;
goto v___jp_3627_;
}
}
}
else
{
lean_object* v___x_3658_; 
lean_del_object(v___x_3638_);
lean_dec(v_searcher_3636_);
v___x_3658_ = lean_box(1);
lean_inc(v___x_3624_);
v_it_3628_ = v___x_3658_;
v_startInclusive_3629_ = v_currPos_3635_;
v_endExclusive_3630_ = v___x_3624_;
goto v___jp_3627_;
}
}
}
else
{
lean_dec(v___x_3624_);
return v_b_3626_;
}
v___jp_3627_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = lean_string_utf8_extract_fast(v_val_3622_, v_startInclusive_3629_, v_endExclusive_3630_);
lean_dec(v_endExclusive_3630_);
lean_dec(v_startInclusive_3629_);
v___x_3632_ = l_Lean_stringToMessageData(v___x_3631_);
v___x_3633_ = lean_array_push(v_b_3626_, v___x_3632_);
v_a_3625_ = v_it_3628_;
v_b_3626_ = v___x_3633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_3660_, lean_object* v___x_3661_, lean_object* v___x_3662_, lean_object* v_a_3663_, lean_object* v_b_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3660_, v___x_3661_, v___x_3662_, v_a_3663_, v_b_3664_);
lean_dec_ref(v___x_3661_);
lean_dec_ref(v_val_3660_);
return v_res_3665_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_3670_ = l_Lean_stringToMessageData(v___x_3669_);
return v___x_3670_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_3673_ = l_Lean_stringToMessageData(v___x_3672_);
return v___x_3673_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_3676_ = l_Lean_stringToMessageData(v___x_3675_);
return v___x_3676_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_3681_ = l_Lean_MessageData_ofFormat(v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_x_3684_, lean_object* v_x_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
if (lean_obj_tag(v_x_3684_) == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = l_List_reverse___redArg(v_x_3685_);
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
return v___x_3690_;
}
else
{
lean_object* v_head_3691_; lean_object* v_tail_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3789_; 
v_head_3691_ = lean_ctor_get(v_x_3684_, 0);
v_tail_3692_ = lean_ctor_get(v_x_3684_, 1);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_x_3684_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3694_ = v_x_3684_;
v_isShared_3695_ = v_isSharedCheck_3789_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_tail_3692_);
lean_inc(v_head_3691_);
lean_dec(v_x_3684_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3789_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_snd_3709_; lean_object* v_fst_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3788_; 
v_snd_3709_ = lean_ctor_get(v_head_3691_, 1);
v_fst_3710_ = lean_ctor_get(v_head_3691_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_head_3691_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3712_ = v_head_3691_;
v_isShared_3713_ = v_isSharedCheck_3788_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_snd_3709_);
lean_inc(v_fst_3710_);
lean_dec(v_head_3691_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3788_;
goto v_resetjp_3711_;
}
v___jp_3696_:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___y_3697_);
lean_ctor_set(v___x_3701_, 1, v___y_3700_);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
lean_ctor_set(v___x_3702_, 1, v___y_3699_);
v___x_3703_ = l_Lean_MessageData_nestD(v___x_3702_);
lean_inc_ref(v___y_3698_);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___y_3698_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v_x_3685_);
lean_ctor_set(v___x_3694_, 0, v___x_3704_);
v___x_3706_ = v___x_3694_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_x_3685_);
v___x_3706_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
v_x_3684_ = v_tail_3692_;
v_x_3685_ = v___x_3706_;
goto _start;
}
}
v_resetjp_3711_:
{
lean_object* v_fst_3714_; lean_object* v_snd_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3787_; 
v_fst_3714_ = lean_ctor_get(v_snd_3709_, 0);
v_snd_3715_ = lean_ctor_get(v_snd_3709_, 1);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_snd_3709_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3717_ = v_snd_3709_;
v_isShared_3718_ = v_isSharedCheck_3787_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_snd_3715_);
lean_inc(v_fst_3714_);
lean_dec(v_snd_3709_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3787_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v_a_3742_; lean_object* v___y_3758_; lean_object* v___x_3767_; 
v___x_3767_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_3683_, v_fst_3710_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Lean_MessageData_nil;
v_a_3742_ = v___x_3768_;
goto v___jp_3741_;
}
else
{
lean_object* v_val_3769_; 
v_val_3769_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_val_3769_);
lean_dec_ref_known(v___x_3767_, 1);
if (lean_obj_tag(v_val_3769_) == 0)
{
lean_object* v_size_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v_size_3770_ = lean_ctor_get(v_val_3769_, 0);
v___x_3771_ = lean_mk_empty_array_with_capacity(v_size_3770_);
v___x_3772_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_3771_, v_val_3769_);
v___x_3773_ = lean_array_get_size(v___x_3772_);
v___x_3778_ = lean_unsigned_to_nat(0u);
v___x_3779_ = lean_nat_dec_eq(v___x_3773_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___y_3783_; uint8_t v___x_3785_; 
v___x_3780_ = lean_unsigned_to_nat(1u);
v___x_3781_ = lean_nat_sub(v___x_3773_, v___x_3780_);
v___x_3785_ = lean_nat_dec_le(v___x_3778_, v___x_3781_);
if (v___x_3785_ == 0)
{
lean_inc(v___x_3781_);
v___y_3783_ = v___x_3781_;
goto v___jp_3782_;
}
else
{
v___y_3783_ = v___x_3778_;
goto v___jp_3782_;
}
v___jp_3782_:
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_nat_dec_le(v___y_3783_, v___x_3781_);
if (v___x_3784_ == 0)
{
lean_dec(v___x_3781_);
lean_inc(v___y_3783_);
v___y_3775_ = v___y_3783_;
v___y_3776_ = v___y_3783_;
goto v___jp_3774_;
}
else
{
v___y_3775_ = v___y_3783_;
v___y_3776_ = v___x_3781_;
goto v___jp_3774_;
}
}
}
else
{
v___y_3758_ = v___x_3772_;
goto v___jp_3757_;
}
v___jp_3774_:
{
lean_object* v___x_3777_; 
v___x_3777_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_3773_, v___x_3772_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
v___y_3758_ = v___x_3777_;
goto v___jp_3757_;
}
}
else
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_MessageData_nil;
v_a_3742_ = v___x_3786_;
goto v___jp_3741_;
}
}
v___jp_3719_:
{
lean_object* v___x_3725_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set_tag(v___x_3717_, 7);
lean_ctor_set(v___x_3717_, 1, v___y_3723_);
lean_ctor_set(v___x_3717_, 0, v___y_3722_);
v___x_3725_ = v___x_3717_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___y_3722_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v___y_3723_);
v___x_3725_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
if (lean_obj_tag(v_snd_3715_) == 0)
{
lean_object* v___x_3726_; 
lean_del_object(v___x_3712_);
v___x_3726_ = l_Lean_MessageData_nil;
v___y_3697_ = v___x_3725_;
v___y_3698_ = v___y_3720_;
v___y_3699_ = v___y_3721_;
v___y_3700_ = v___x_3726_;
goto v___jp_3696_;
}
else
{
lean_object* v_val_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
v_val_3727_ = lean_ctor_get(v_snd_3715_, 0);
lean_inc_n(v_val_3727_, 2);
lean_dec_ref_known(v_snd_3715_, 1);
v___x_3728_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0);
v___x_3729_ = lean_unsigned_to_nat(0u);
v___x_3730_ = lean_string_utf8_byte_size(v_val_3727_);
v___x_3731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3731_, 0, v_val_3727_);
lean_ctor_set(v___x_3731_, 1, v___x_3729_);
lean_ctor_set(v___x_3731_, 2, v___x_3730_);
v___x_3732_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0);
v___x_3733_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_3734_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3727_, v___x_3731_, v___x_3730_, v___x_3732_, v___x_3733_);
lean_dec_ref_known(v___x_3731_, 3);
lean_dec(v_val_3727_);
v___x_3735_ = lean_array_to_list(v___x_3734_);
v___x_3736_ = l_Lean_MessageData_joinSep(v___x_3735_, v___x_3728_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set_tag(v___x_3712_, 7);
lean_ctor_set(v___x_3712_, 1, v___x_3736_);
lean_ctor_set(v___x_3712_, 0, v___x_3728_);
v___x_3738_ = v___x_3712_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3728_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
v___y_3697_ = v___x_3725_;
v___y_3698_ = v___y_3720_;
v___y_3699_ = v___y_3721_;
v___y_3700_ = v___x_3738_;
goto v___jp_3696_;
}
}
}
}
v___jp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3743_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_3744_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5);
lean_inc(v_fst_3710_);
v___x_3745_ = l_Lean_MessageData_ofName(v_fst_3710_);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set(v___x_3747_, 1, v___x_3744_);
v___x_3748_ = 1;
v___x_3749_ = l_Lean_Name_toString(v_fst_3710_, v___x_3748_);
v___x_3750_ = lean_string_dec_eq(v___x_3749_, v_fst_3714_);
lean_dec_ref(v___x_3749_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3751_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_3752_ = l_Lean_stringToMessageData(v_fst_3714_);
v___x_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_3755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___y_3720_ = v___x_3743_;
v___y_3721_ = v_a_3742_;
v___y_3722_ = v___x_3747_;
v___y_3723_ = v___x_3755_;
goto v___jp_3719_;
}
else
{
lean_object* v___x_3756_; 
lean_dec(v_fst_3714_);
v___x_3756_ = l_Lean_MessageData_nil;
v___y_3720_ = v___x_3743_;
v___y_3721_ = v_a_3742_;
v___y_3722_ = v___x_3747_;
v___y_3723_ = v___x_3756_;
goto v___jp_3719_;
}
}
v___jp_3757_:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = lean_array_to_list(v___y_3758_);
v___x_3760_ = lean_box(0);
v___x_3761_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_3682_, v___x_3759_, v___x_3760_, v___y_3686_, v___y_3687_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v___x_3763_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0);
v___x_3764_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_3765_ = l_Lean_MessageData_joinSep(v_a_3762_, v___x_3764_);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3763_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v_a_3742_ = v___x_3766_;
goto v___jp_3741_;
}
else
{
lean_del_object(v___x_3717_);
lean_dec(v_snd_3715_);
lean_dec(v_fst_3714_);
lean_del_object(v___x_3712_);
lean_dec(v_fst_3710_);
lean_del_object(v___x_3694_);
lean_dec(v_tail_3692_);
lean_dec(v_x_3685_);
return v___x_3761_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_x_3792_, lean_object* v_x_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3790_, v_a_3791_, v_x_3792_, v_x_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v_a_3791_);
lean_dec(v_a_3790_);
return v_res_3797_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v_suppressElabErrors_3798_, uint8_t v___y_3799_, lean_object* v_x_3800_){
_start:
{
if (lean_obj_tag(v_x_3800_) == 1)
{
lean_object* v_pre_3801_; 
v_pre_3801_ = lean_ctor_get(v_x_3800_, 0);
if (lean_obj_tag(v_pre_3801_) == 0)
{
lean_object* v_str_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_str_3802_ = lean_ctor_get(v_x_3800_, 1);
v___x_3803_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1___lam__0___closed__0));
v___x_3804_ = lean_string_dec_eq(v_str_3802_, v___x_3803_);
if (v___x_3804_ == 0)
{
return v___x_3804_;
}
else
{
return v_suppressElabErrors_3798_;
}
}
else
{
return v___y_3799_;
}
}
else
{
return v___y_3799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v_suppressElabErrors_3805_, lean_object* v___y_3806_, lean_object* v_x_3807_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3808_; uint8_t v___y_17927__boxed_3809_; uint8_t v_res_3810_; lean_object* v_r_3811_; 
v_suppressElabErrors_boxed_3808_ = lean_unbox(v_suppressElabErrors_3805_);
v___y_17927__boxed_3809_ = lean_unbox(v___y_3806_);
v_res_3810_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v_suppressElabErrors_boxed_3808_, v___y_17927__boxed_3809_, v_x_3807_);
lean_dec(v_x_3807_);
v_r_3811_ = lean_box(v_res_3810_);
return v_r_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_3812_, lean_object* v_msgData_3813_, uint8_t v_severity_3814_, uint8_t v_isSilent_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; uint8_t v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; uint8_t v___y_3826_; lean_object* v___y_3827_; uint8_t v___y_3885_; uint8_t v___y_3886_; lean_object* v___y_3887_; uint8_t v___y_3888_; lean_object* v___y_3889_; uint8_t v___y_3913_; uint8_t v___y_3914_; uint8_t v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; uint8_t v___y_3921_; uint8_t v___y_3922_; uint8_t v___y_3923_; uint8_t v___x_3938_; uint8_t v___y_3940_; uint8_t v___y_3941_; uint8_t v___y_3942_; uint8_t v___y_3944_; uint8_t v___x_3956_; 
v___x_3938_ = 2;
v___x_3956_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3814_, v___x_3938_);
if (v___x_3956_ == 0)
{
v___y_3944_ = v___x_3956_;
goto v___jp_3943_;
}
else
{
uint8_t v___x_3957_; 
lean_inc_ref(v_msgData_3813_);
v___x_3957_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3813_);
v___y_3944_ = v___x_3957_;
goto v___jp_3943_;
}
v___jp_3819_:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_Elab_Command_getScope___redArg(v___y_3827_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v_currNamespace_3830_; lean_object* v___x_3831_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3828_, 1);
v_currNamespace_3830_ = lean_ctor_get(v_a_3829_, 2);
lean_inc(v_currNamespace_3830_);
lean_dec(v_a_3829_);
v___x_3831_ = l_Lean_Elab_Command_getScope___redArg(v___y_3827_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3867_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3867_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3867_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v_openDecls_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v_env_3841_; lean_object* v_messages_3842_; lean_object* v_scopes_3843_; lean_object* v_usedQuotCtxts_3844_; lean_object* v_nextMacroScope_3845_; lean_object* v_maxRecDepth_3846_; lean_object* v_ngen_3847_; lean_object* v_auxDeclNGen_3848_; lean_object* v_infoState_3849_; lean_object* v_traceState_3850_; lean_object* v_snapshotTasks_3851_; lean_object* v_prevLinterStates_3852_; lean_object* v_codeQualityEntryTasks_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3866_; 
v_openDecls_3836_ = lean_ctor_get(v_a_3832_, 3);
lean_inc(v_openDecls_3836_);
lean_dec(v_a_3832_);
v___x_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3837_, 0, v_currNamespace_3830_);
lean_ctor_set(v___x_3837_, 1, v_openDecls_3836_);
v___x_3838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
lean_ctor_set(v___x_3838_, 1, v___y_3825_);
lean_inc_ref(v___y_3824_);
lean_inc_ref(v___y_3820_);
v___x_3839_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3839_, 0, v___y_3820_);
lean_ctor_set(v___x_3839_, 1, v___y_3822_);
lean_ctor_set(v___x_3839_, 2, v___y_3821_);
lean_ctor_set(v___x_3839_, 3, v___y_3824_);
lean_ctor_set(v___x_3839_, 4, v___x_3838_);
lean_ctor_set_uint8(v___x_3839_, sizeof(void*)*5, v___y_3826_);
lean_ctor_set_uint8(v___x_3839_, sizeof(void*)*5 + 1, v___y_3823_);
lean_ctor_set_uint8(v___x_3839_, sizeof(void*)*5 + 2, v_isSilent_3815_);
v___x_3840_ = lean_st_ref_take(v___y_3827_);
v_env_3841_ = lean_ctor_get(v___x_3840_, 0);
v_messages_3842_ = lean_ctor_get(v___x_3840_, 1);
v_scopes_3843_ = lean_ctor_get(v___x_3840_, 2);
v_usedQuotCtxts_3844_ = lean_ctor_get(v___x_3840_, 3);
v_nextMacroScope_3845_ = lean_ctor_get(v___x_3840_, 4);
v_maxRecDepth_3846_ = lean_ctor_get(v___x_3840_, 5);
v_ngen_3847_ = lean_ctor_get(v___x_3840_, 6);
v_auxDeclNGen_3848_ = lean_ctor_get(v___x_3840_, 7);
v_infoState_3849_ = lean_ctor_get(v___x_3840_, 8);
v_traceState_3850_ = lean_ctor_get(v___x_3840_, 9);
v_snapshotTasks_3851_ = lean_ctor_get(v___x_3840_, 10);
v_prevLinterStates_3852_ = lean_ctor_get(v___x_3840_, 11);
v_codeQualityEntryTasks_3853_ = lean_ctor_get(v___x_3840_, 12);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3855_ = v___x_3840_;
v_isShared_3856_ = v_isSharedCheck_3866_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3853_);
lean_inc(v_prevLinterStates_3852_);
lean_inc(v_snapshotTasks_3851_);
lean_inc(v_traceState_3850_);
lean_inc(v_infoState_3849_);
lean_inc(v_auxDeclNGen_3848_);
lean_inc(v_ngen_3847_);
lean_inc(v_maxRecDepth_3846_);
lean_inc(v_nextMacroScope_3845_);
lean_inc(v_usedQuotCtxts_3844_);
lean_inc(v_scopes_3843_);
lean_inc(v_messages_3842_);
lean_inc(v_env_3841_);
lean_dec(v___x_3840_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3866_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3857_ = lean_box(0);
v___x_3858_ = l_Lean_MessageLog_add(v___x_3839_, v_messages_3842_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 1, v___x_3858_);
v___x_3860_ = v___x_3855_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_env_3841_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_scopes_3843_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_usedQuotCtxts_3844_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v_nextMacroScope_3845_);
lean_ctor_set(v_reuseFailAlloc_3865_, 5, v_maxRecDepth_3846_);
lean_ctor_set(v_reuseFailAlloc_3865_, 6, v_ngen_3847_);
lean_ctor_set(v_reuseFailAlloc_3865_, 7, v_auxDeclNGen_3848_);
lean_ctor_set(v_reuseFailAlloc_3865_, 8, v_infoState_3849_);
lean_ctor_set(v_reuseFailAlloc_3865_, 9, v_traceState_3850_);
lean_ctor_set(v_reuseFailAlloc_3865_, 10, v_snapshotTasks_3851_);
lean_ctor_set(v_reuseFailAlloc_3865_, 11, v_prevLinterStates_3852_);
lean_ctor_set(v_reuseFailAlloc_3865_, 12, v_codeQualityEntryTasks_3853_);
v___x_3860_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3861_ = lean_st_ref_put(v___y_3827_, v___x_3860_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 0, v___x_3857_);
v___x_3863_ = v___x_3834_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3857_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v_currNamespace_3830_);
lean_dec_ref(v___y_3825_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
v_a_3868_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3831_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3831_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_dec_ref(v___y_3825_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
v_a_3876_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3828_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3828_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
v___jp_3884_:
{
lean_object* v_fileName_3890_; lean_object* v_fileMap_3891_; uint8_t v_suppressElabErrors_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___f_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3911_; 
v_fileName_3890_ = lean_ctor_get(v___y_3816_, 0);
v_fileMap_3891_ = lean_ctor_get(v___y_3816_, 1);
v_suppressElabErrors_3892_ = lean_ctor_get_uint8(v___y_3816_, sizeof(void*)*10);
v___x_3893_ = lean_box(v_suppressElabErrors_3892_);
v___x_3894_ = lean_box(v___y_3885_);
v___f_3895_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3895_, 0, v___x_3893_);
lean_closure_set(v___f_3895_, 1, v___x_3894_);
v___x_3896_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3813_);
v___x_3897_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__4___redArg(v___x_3896_, v___y_3817_);
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3911_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3911_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_inc_ref_n(v_fileMap_3891_, 2);
v___x_3902_ = l_Lean_FileMap_toPosition(v_fileMap_3891_, v___y_3887_);
lean_dec(v___y_3887_);
v___x_3903_ = l_Lean_FileMap_toPosition(v_fileMap_3891_, v___y_3889_);
lean_dec(v___y_3889_);
v___x_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
v___x_3905_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__2_spec__5___closed__7));
if (v_suppressElabErrors_3892_ == 0)
{
lean_del_object(v___x_3900_);
lean_dec_ref(v___f_3895_);
v___y_3820_ = v_fileName_3890_;
v___y_3821_ = v___x_3904_;
v___y_3822_ = v___x_3902_;
v___y_3823_ = v___y_3886_;
v___y_3824_ = v___x_3905_;
v___y_3825_ = v_a_3898_;
v___y_3826_ = v___y_3888_;
v___y_3827_ = v___y_3817_;
goto v___jp_3819_;
}
else
{
uint8_t v___x_3906_; 
lean_inc(v_a_3898_);
v___x_3906_ = l_Lean_MessageData_hasTag(v___f_3895_, v_a_3898_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
lean_dec_ref_known(v___x_3904_, 1);
lean_dec_ref(v___x_3902_);
lean_dec(v_a_3898_);
v___x_3907_ = lean_box(0);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3907_);
v___x_3909_ = v___x_3900_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
else
{
lean_del_object(v___x_3900_);
v___y_3820_ = v_fileName_3890_;
v___y_3821_ = v___x_3904_;
v___y_3822_ = v___x_3902_;
v___y_3823_ = v___y_3886_;
v___y_3824_ = v___x_3905_;
v___y_3825_ = v_a_3898_;
v___y_3826_ = v___y_3888_;
v___y_3827_ = v___y_3817_;
goto v___jp_3819_;
}
}
}
}
v___jp_3912_:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lean_Syntax_getTailPos_x3f(v___y_3916_, v___y_3915_);
lean_dec(v___y_3916_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_inc(v___y_3917_);
v___y_3885_ = v___y_3913_;
v___y_3886_ = v___y_3914_;
v___y_3887_ = v___y_3917_;
v___y_3888_ = v___y_3915_;
v___y_3889_ = v___y_3917_;
goto v___jp_3884_;
}
else
{
lean_object* v_val_3919_; 
v_val_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_val_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___y_3885_ = v___y_3913_;
v___y_3886_ = v___y_3914_;
v___y_3887_ = v___y_3917_;
v___y_3888_ = v___y_3915_;
v___y_3889_ = v_val_3919_;
goto v___jp_3884_;
}
}
v___jp_3920_:
{
lean_object* v___x_3924_; 
v___x_3924_ = l_Lean_Elab_Command_getRef___redArg(v___y_3816_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v_ref_3926_; lean_object* v___x_3927_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v_ref_3926_ = l_Lean_replaceRef(v_ref_3812_, v_a_3925_);
lean_dec(v_a_3925_);
v___x_3927_ = l_Lean_Syntax_getPos_x3f(v_ref_3926_, v___y_3922_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_unsigned_to_nat(0u);
v___y_3913_ = v___y_3921_;
v___y_3914_ = v___y_3923_;
v___y_3915_ = v___y_3922_;
v___y_3916_ = v_ref_3926_;
v___y_3917_ = v___x_3928_;
goto v___jp_3912_;
}
else
{
lean_object* v_val_3929_; 
v_val_3929_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_val_3929_);
lean_dec_ref_known(v___x_3927_, 1);
v___y_3913_ = v___y_3921_;
v___y_3914_ = v___y_3923_;
v___y_3915_ = v___y_3922_;
v___y_3916_ = v_ref_3926_;
v___y_3917_ = v_val_3929_;
goto v___jp_3912_;
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref(v_msgData_3813_);
v_a_3930_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3924_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3924_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
v___jp_3939_:
{
if (v___y_3942_ == 0)
{
v___y_3921_ = v___y_3940_;
v___y_3922_ = v___y_3941_;
v___y_3923_ = v_severity_3814_;
goto v___jp_3920_;
}
else
{
v___y_3921_ = v___y_3940_;
v___y_3922_ = v___y_3941_;
v___y_3923_ = v___x_3938_;
goto v___jp_3920_;
}
}
v___jp_3943_:
{
if (v___y_3944_ == 0)
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v_scopes_3947_; lean_object* v___x_3948_; lean_object* v_opts_3949_; uint8_t v___x_3950_; uint8_t v___x_3951_; 
v___x_3945_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3946_ = lean_st_ref_get(v___y_3817_);
v_scopes_3947_ = lean_ctor_get(v___x_3946_, 2);
lean_inc(v_scopes_3947_);
lean_dec(v___x_3946_);
v___x_3948_ = l_List_head_x21___redArg(v___x_3945_, v_scopes_3947_);
lean_dec(v_scopes_3947_);
v_opts_3949_ = lean_ctor_get(v___x_3948_, 1);
lean_inc_ref(v_opts_3949_);
lean_dec(v___x_3948_);
v___x_3950_ = 1;
v___x_3951_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3814_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_dec_ref(v_opts_3949_);
v___y_3940_ = v___y_3944_;
v___y_3941_ = v___y_3944_;
v___y_3942_ = v___x_3951_;
goto v___jp_3939_;
}
else
{
lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3952_ = l_Lean_warningAsError;
v___x_3953_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__10(v_opts_3949_, v___x_3952_);
lean_dec_ref(v_opts_3949_);
v___y_3940_ = v___y_3944_;
v___y_3941_ = v___y_3944_;
v___y_3942_ = v___x_3953_;
goto v___jp_3939_;
}
}
else
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec_ref(v_msgData_3813_);
v___x_3954_ = lean_box(0);
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
return v___x_3955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_3958_, lean_object* v_msgData_3959_, lean_object* v_severity_3960_, lean_object* v_isSilent_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
uint8_t v_severity_boxed_3965_; uint8_t v_isSilent_boxed_3966_; lean_object* v_res_3967_; 
v_severity_boxed_3965_ = lean_unbox(v_severity_3960_);
v_isSilent_boxed_3966_ = lean_unbox(v_isSilent_3961_);
v_res_3967_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_3958_, v_msgData_3959_, v_severity_boxed_3965_, v_isSilent_boxed_3966_, v___y_3962_, v___y_3963_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v_ref_3958_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_3968_, uint8_t v_severity_3969_, uint8_t v_isSilent_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = l_Lean_Elab_Command_getRef___redArg(v___y_3971_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3976_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v___x_3974_, 1);
v___x_3976_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_3975_, v_msgData_3968_, v_severity_3969_, v_isSilent_3970_, v___y_3971_, v___y_3972_);
lean_dec(v_a_3975_);
return v___x_3976_;
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v_msgData_3968_);
v_a_3977_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3974_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3974_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_3985_, lean_object* v_severity_3986_, lean_object* v_isSilent_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
uint8_t v_severity_boxed_3991_; uint8_t v_isSilent_boxed_3992_; lean_object* v_res_3993_; 
v_severity_boxed_3991_ = lean_unbox(v_severity_3986_);
v_isSilent_boxed_3992_ = lean_unbox(v_isSilent_3987_);
v_res_3993_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3985_, v_severity_boxed_3991_, v_isSilent_boxed_3992_, v___y_3988_, v___y_3989_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
uint8_t v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = 0;
v___x_3999_ = 0;
v___x_4000_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_3994_, v___x_3998_, v___x_3999_, v___y_3995_, v___y_3996_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_4006_, lean_object* v_x_4007_){
_start:
{
if (lean_obj_tag(v_x_4007_) == 0)
{
lean_object* v_k_4009_; lean_object* v_v_4010_; lean_object* v_l_4011_; lean_object* v_r_4012_; lean_object* v___x_4013_; lean_object* v_a_4014_; lean_object* v_a_4015_; lean_object* v___x_4016_; 
v_k_4009_ = lean_ctor_get(v_x_4007_, 1);
lean_inc(v_k_4009_);
v_v_4010_ = lean_ctor_get(v_x_4007_, 2);
lean_inc(v_v_4010_);
v_l_4011_ = lean_ctor_get(v_x_4007_, 3);
lean_inc(v_l_4011_);
v_r_4012_ = lean_ctor_get(v_x_4007_, 4);
lean_inc(v_r_4012_);
lean_dec_ref_known(v_x_4007_, 5);
v___x_4013_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_4006_, v_l_4011_);
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref(v___x_4013_);
v_a_4015_ = lean_ctor_get(v_a_4014_, 0);
lean_inc(v_a_4015_);
lean_dec(v_a_4014_);
v___x_4016_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4009_, v_v_4010_, v_a_4015_);
v_init_4006_ = v___x_4016_;
v_x_4007_ = v_r_4012_;
goto _start;
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4018_, 0, v_init_4006_);
v___x_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
return v___x_4019_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_4020_, lean_object* v_x_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_4020_, v_x_4021_);
return v_res_4023_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_4024_, lean_object* v_x1_4025_, lean_object* v_x2_4026_){
_start:
{
lean_object* v_fst_4027_; lean_object* v_fst_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; 
v_fst_4027_ = lean_ctor_get(v_x1_4025_, 0);
lean_inc(v_fst_4027_);
lean_dec_ref(v_x1_4025_);
v_fst_4028_ = lean_ctor_get(v_x2_4026_, 0);
lean_inc(v_fst_4028_);
lean_dec_ref(v_x2_4026_);
v___x_4029_ = l_Lean_Name_toString(v_fst_4027_, v___x_4024_);
v___x_4030_ = l_Lean_Name_toString(v_fst_4028_, v___x_4024_);
v___x_4031_ = lean_string_dec_lt(v___x_4029_, v___x_4030_);
lean_dec_ref(v___x_4030_);
lean_dec_ref(v___x_4029_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_4032_, lean_object* v_x1_4033_, lean_object* v_x2_4034_){
_start:
{
uint8_t v___x_18269__boxed_4035_; uint8_t v_res_4036_; lean_object* v_r_4037_; 
v___x_18269__boxed_4035_ = lean_unbox(v___x_4032_);
v_res_4036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18269__boxed_4035_, v_x1_4033_, v_x2_4034_);
v_r_4037_ = lean_box(v_res_4036_);
return v_r_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_4038_, lean_object* v_pivot_4039_, lean_object* v_as_4040_, lean_object* v_i_4041_, lean_object* v_k_4042_){
_start:
{
uint8_t v___x_4043_; 
v___x_4043_ = lean_nat_dec_lt(v_k_4042_, v_hi_4038_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
lean_dec(v_k_4042_);
lean_dec_ref(v_pivot_4039_);
v___x_4044_ = lean_array_fswap(v_as_4040_, v_i_4041_, v_hi_4038_);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v_i_4041_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
return v___x_4045_;
}
else
{
lean_object* v___x_4046_; lean_object* v_fst_4047_; lean_object* v_fst_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v___x_4046_ = lean_array_fget_borrowed(v_as_4040_, v_k_4042_);
v_fst_4047_ = lean_ctor_get(v___x_4046_, 0);
v_fst_4048_ = lean_ctor_get(v_pivot_4039_, 0);
lean_inc(v_fst_4047_);
v___x_4049_ = l_Lean_Name_toString(v_fst_4047_, v___x_4043_);
lean_inc(v_fst_4048_);
v___x_4050_ = l_Lean_Name_toString(v_fst_4048_, v___x_4043_);
v___x_4051_ = lean_string_dec_lt(v___x_4049_, v___x_4050_);
lean_dec_ref(v___x_4050_);
lean_dec_ref(v___x_4049_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_unsigned_to_nat(1u);
v___x_4053_ = lean_nat_add(v_k_4042_, v___x_4052_);
lean_dec(v_k_4042_);
v_k_4042_ = v___x_4053_;
goto _start;
}
else
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4055_ = lean_array_fswap(v_as_4040_, v_i_4041_, v_k_4042_);
v___x_4056_ = lean_unsigned_to_nat(1u);
v___x_4057_ = lean_nat_add(v_i_4041_, v___x_4056_);
lean_dec(v_i_4041_);
v___x_4058_ = lean_nat_add(v_k_4042_, v___x_4056_);
lean_dec(v_k_4042_);
v_as_4040_ = v___x_4055_;
v_i_4041_ = v___x_4057_;
v_k_4042_ = v___x_4058_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_4060_, lean_object* v_pivot_4061_, lean_object* v_as_4062_, lean_object* v_i_4063_, lean_object* v_k_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_4060_, v_pivot_4061_, v_as_4062_, v_i_4063_, v_k_4064_);
lean_dec(v_hi_4060_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_4066_, lean_object* v_as_4067_, lean_object* v_lo_4068_, lean_object* v_hi_4069_){
_start:
{
lean_object* v___y_4071_; uint8_t v___x_4081_; 
v___x_4081_ = lean_nat_dec_lt(v_lo_4068_, v_hi_4069_);
if (v___x_4081_ == 0)
{
lean_dec(v_lo_4068_);
return v_as_4067_;
}
else
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v_mid_4084_; lean_object* v___y_4086_; lean_object* v___y_4092_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v___x_4082_ = lean_nat_add(v_lo_4068_, v_hi_4069_);
v___x_4083_ = lean_unsigned_to_nat(1u);
v_mid_4084_ = lean_nat_shiftr(v___x_4082_, v___x_4083_);
lean_dec(v___x_4082_);
v___x_4097_ = lean_array_fget_borrowed(v_as_4067_, v_mid_4084_);
v___x_4098_ = lean_array_fget_borrowed(v_as_4067_, v_lo_4068_);
lean_inc(v___x_4098_);
lean_inc(v___x_4097_);
v___x_4099_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_4081_, v___x_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
v___y_4092_ = v_as_4067_;
goto v___jp_4091_;
}
else
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_array_fswap(v_as_4067_, v_lo_4068_, v_mid_4084_);
v___y_4092_ = v___x_4100_;
goto v___jp_4091_;
}
v___jp_4085_:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; 
v___x_4087_ = lean_array_fget_borrowed(v___y_4086_, v_mid_4084_);
v___x_4088_ = lean_array_fget_borrowed(v___y_4086_, v_hi_4069_);
lean_inc(v___x_4088_);
lean_inc(v___x_4087_);
v___x_4089_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_4081_, v___x_4087_, v___x_4088_);
if (v___x_4089_ == 0)
{
lean_dec(v_mid_4084_);
v___y_4071_ = v___y_4086_;
goto v___jp_4070_;
}
else
{
lean_object* v___x_4090_; 
v___x_4090_ = lean_array_fswap(v___y_4086_, v_mid_4084_, v_hi_4069_);
lean_dec(v_mid_4084_);
v___y_4071_ = v___x_4090_;
goto v___jp_4070_;
}
}
v___jp_4091_:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v___x_4093_ = lean_array_fget_borrowed(v___y_4092_, v_hi_4069_);
v___x_4094_ = lean_array_fget_borrowed(v___y_4092_, v_lo_4068_);
lean_inc(v___x_4094_);
lean_inc(v___x_4093_);
v___x_4095_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_4081_, v___x_4093_, v___x_4094_);
if (v___x_4095_ == 0)
{
v___y_4086_ = v___y_4092_;
goto v___jp_4085_;
}
else
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_array_fswap(v___y_4092_, v_lo_4068_, v_hi_4069_);
v___y_4086_ = v___x_4096_;
goto v___jp_4085_;
}
}
}
v___jp_4070_:
{
lean_object* v_pivot_4072_; lean_object* v___x_4073_; lean_object* v_fst_4074_; lean_object* v_snd_4075_; uint8_t v___x_4076_; 
v_pivot_4072_ = lean_array_fget(v___y_4071_, v_hi_4069_);
lean_inc_n(v_lo_4068_, 2);
v___x_4073_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_4069_, v_pivot_4072_, v___y_4071_, v_lo_4068_, v_lo_4068_);
v_fst_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_fst_4074_);
v_snd_4075_ = lean_ctor_get(v___x_4073_, 1);
lean_inc(v_snd_4075_);
lean_dec_ref(v___x_4073_);
v___x_4076_ = lean_nat_dec_le(v_hi_4069_, v_fst_4074_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_4066_, v_snd_4075_, v_lo_4068_, v_fst_4074_);
v___x_4078_ = lean_unsigned_to_nat(1u);
v___x_4079_ = lean_nat_add(v_fst_4074_, v___x_4078_);
lean_dec(v_fst_4074_);
v_as_4067_ = v___x_4077_;
v_lo_4068_ = v___x_4079_;
goto _start;
}
else
{
lean_dec(v_fst_4074_);
lean_dec(v_lo_4068_);
return v_snd_4075_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_4101_, lean_object* v_as_4102_, lean_object* v_lo_4103_, lean_object* v_hi_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_4101_, v_as_4102_, v_lo_4103_, v_hi_4104_);
lean_dec(v_hi_4104_);
lean_dec(v_n_4101_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_4106_, lean_object* v_x_4107_){
_start:
{
if (lean_obj_tag(v_x_4107_) == 0)
{
lean_object* v_k_4108_; lean_object* v_v_4109_; lean_object* v_l_4110_; lean_object* v_r_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v_k_4108_ = lean_ctor_get(v_x_4107_, 1);
v_v_4109_ = lean_ctor_get(v_x_4107_, 2);
v_l_4110_ = lean_ctor_get(v_x_4107_, 3);
v_r_4111_ = lean_ctor_get(v_x_4107_, 4);
v___x_4112_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_4106_, v_l_4110_);
lean_inc(v_v_4109_);
lean_inc(v_k_4108_);
v___x_4113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4113_, 0, v_k_4108_);
lean_ctor_set(v___x_4113_, 1, v_v_4109_);
v___x_4114_ = lean_array_push(v___x_4112_, v___x_4113_);
v_init_4106_ = v___x_4114_;
v_x_4107_ = v_r_4111_;
goto _start;
}
else
{
return v_init_4106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_4116_, lean_object* v_x_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_4116_, v_x_4117_);
lean_dec(v_x_4117_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_4119_, size_t v_sz_4120_, size_t v_i_4121_, lean_object* v_b_4122_){
_start:
{
uint8_t v___x_4124_; 
v___x_4124_ = lean_usize_dec_lt(v_i_4121_, v_sz_4120_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_b_4122_);
return v___x_4125_;
}
else
{
lean_object* v_a_4126_; lean_object* v_fst_4127_; lean_object* v_snd_4128_; lean_object* v_found_4129_; size_t v___x_4130_; size_t v___x_4131_; 
v_a_4126_ = lean_array_uget_borrowed(v_as_4119_, v_i_4121_);
v_fst_4127_ = lean_ctor_get(v_a_4126_, 0);
v_snd_4128_ = lean_ctor_get(v_a_4126_, 1);
lean_inc(v_snd_4128_);
lean_inc(v_fst_4127_);
v_found_4129_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4127_, v_snd_4128_, v_b_4122_);
v___x_4130_ = ((size_t)1ULL);
v___x_4131_ = lean_usize_add(v_i_4121_, v___x_4130_);
v_i_4121_ = v___x_4131_;
v_b_4122_ = v_found_4129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_4133_, lean_object* v_sz_4134_, lean_object* v_i_4135_, lean_object* v_b_4136_, lean_object* v___y_4137_){
_start:
{
size_t v_sz_boxed_4138_; size_t v_i_boxed_4139_; lean_object* v_res_4140_; 
v_sz_boxed_4138_ = lean_unbox_usize(v_sz_4134_);
lean_dec(v_sz_4134_);
v_i_boxed_4139_ = lean_unbox_usize(v_i_4135_);
lean_dec(v_i_4135_);
v_res_4140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_4133_, v_sz_boxed_4138_, v_i_boxed_4139_, v_b_4136_);
lean_dec_ref(v_as_4133_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_4141_, size_t v_sz_4142_, size_t v_i_4143_, lean_object* v_b_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
uint8_t v___x_4148_; 
v___x_4148_ = lean_usize_dec_lt(v_i_4143_, v_sz_4142_);
if (v___x_4148_ == 0)
{
lean_object* v___x_4149_; 
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_b_4144_);
return v___x_4149_;
}
else
{
lean_object* v_a_4150_; size_t v_sz_4151_; size_t v___x_4152_; lean_object* v___x_4153_; 
v_a_4150_ = lean_array_uget_borrowed(v_as_4141_, v_i_4143_);
v_sz_4151_ = lean_array_size(v_a_4150_);
v___x_4152_ = ((size_t)0ULL);
v___x_4153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_4150_, v_sz_4151_, v___x_4152_, v_b_4144_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; size_t v___x_4155_; size_t v___x_4156_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v___x_4155_ = ((size_t)1ULL);
v___x_4156_ = lean_usize_add(v_i_4143_, v___x_4155_);
v_i_4143_ = v___x_4156_;
v_b_4144_ = v_a_4154_;
goto _start;
}
else
{
return v___x_4153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_4158_, lean_object* v_sz_4159_, lean_object* v_i_4160_, lean_object* v_b_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
size_t v_sz_boxed_4165_; size_t v_i_boxed_4166_; lean_object* v_res_4167_; 
v_sz_boxed_4165_ = lean_unbox_usize(v_sz_4159_);
lean_dec(v_sz_4159_);
v_i_boxed_4166_ = lean_unbox_usize(v_i_4160_);
lean_dec(v_i_4160_);
v_res_4167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_4158_, v_sz_boxed_4165_, v_i_boxed_4166_, v_b_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec_ref(v_as_4158_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___y_4174_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v_env_4192_; lean_object* v___x_4193_; lean_object* v_toEnvExtension_4194_; lean_object* v_asyncMode_4195_; lean_object* v___x_4196_; lean_object* v_a_4198_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v_a_4223_; lean_object* v_a_4224_; 
v___x_4189_ = lean_box(1);
v___x_4190_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4191_ = lean_st_ref_get(v___y_4171_);
v_env_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc_ref_n(v_env_4192_, 2);
lean_dec(v___x_4191_);
v___x_4193_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_4194_ = lean_ctor_get(v___x_4193_, 0);
v_asyncMode_4195_ = lean_ctor_get(v_toEnvExtension_4194_, 2);
v___x_4196_ = lean_box(0);
v___x_4221_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4189_, v___x_4193_, v_env_4192_, v_asyncMode_4195_, v___x_4196_);
v___x_4222_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_4189_, v___x_4221_);
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref(v___x_4222_);
v_a_4224_ = lean_ctor_get(v_a_4223_, 0);
lean_inc(v_a_4224_);
lean_dec(v_a_4223_);
v_a_4198_ = v_a_4224_;
goto v___jp_4197_;
v___jp_4173_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = lean_array_to_list(v___y_4174_);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
v___jp_4177_:
{
lean_object* v___x_4182_; 
v___x_4182_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_4180_, v___y_4179_, v___y_4178_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec(v___y_4180_);
v___y_4174_ = v___x_4182_;
goto v___jp_4173_;
}
v___jp_4183_:
{
uint8_t v___x_4188_; 
v___x_4188_ = lean_nat_dec_le(v___y_4187_, v___y_4184_);
if (v___x_4188_ == 0)
{
lean_dec(v___y_4184_);
lean_inc(v___y_4187_);
v___y_4178_ = v___y_4187_;
v___y_4179_ = v___y_4185_;
v___y_4180_ = v___y_4186_;
v___y_4181_ = v___y_4187_;
goto v___jp_4177_;
}
else
{
v___y_4178_ = v___y_4187_;
v___y_4179_ = v___y_4185_;
v___y_4180_ = v___y_4186_;
v___y_4181_ = v___y_4184_;
goto v___jp_4177_;
}
}
v___jp_4197_:
{
lean_object* v___x_4199_; lean_object* v_importedEntries_4200_; size_t v_sz_4201_; size_t v___x_4202_; lean_object* v___x_4203_; 
v___x_4199_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4190_, v_toEnvExtension_4194_, v_env_4192_, v_asyncMode_4195_, v___x_4196_);
v_importedEntries_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc_ref(v_importedEntries_4200_);
lean_dec(v___x_4199_);
v_sz_4201_ = lean_array_size(v_importedEntries_4200_);
v___x_4202_ = ((size_t)0ULL);
v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_4200_, v_sz_4201_, v___x_4202_, v_a_4198_, v___y_4170_, v___y_4171_);
lean_dec_ref(v_importedEntries_4200_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v_arr_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0));
v_arr_4207_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_4206_, v_a_4204_);
lean_dec(v_a_4204_);
v___x_4208_ = lean_array_get_size(v_arr_4207_);
v___x_4209_ = lean_nat_dec_eq(v___x_4208_, v___x_4205_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; 
v___x_4210_ = lean_unsigned_to_nat(1u);
v___x_4211_ = lean_nat_sub(v___x_4208_, v___x_4210_);
v___x_4212_ = lean_nat_dec_le(v___x_4205_, v___x_4211_);
if (v___x_4212_ == 0)
{
lean_inc(v___x_4211_);
v___y_4184_ = v___x_4211_;
v___y_4185_ = v_arr_4207_;
v___y_4186_ = v___x_4208_;
v___y_4187_ = v___x_4211_;
goto v___jp_4183_;
}
else
{
v___y_4184_ = v___x_4211_;
v___y_4185_ = v_arr_4207_;
v___y_4186_ = v___x_4208_;
v___y_4187_ = v___x_4205_;
goto v___jp_4183_;
}
}
else
{
v___y_4174_ = v_arr_4207_;
goto v___jp_4173_;
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
v_a_4213_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4203_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4203_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_4229_, lean_object* v_k_4230_, lean_object* v_fallback_4231_){
_start:
{
if (lean_obj_tag(v_t_4229_) == 0)
{
lean_object* v_k_4232_; lean_object* v_v_4233_; lean_object* v_l_4234_; lean_object* v_r_4235_; uint8_t v___x_4236_; 
v_k_4232_ = lean_ctor_get(v_t_4229_, 1);
v_v_4233_ = lean_ctor_get(v_t_4229_, 2);
v_l_4234_ = lean_ctor_get(v_t_4229_, 3);
v_r_4235_ = lean_ctor_get(v_t_4229_, 4);
v___x_4236_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4230_, v_k_4232_);
switch(v___x_4236_)
{
case 0:
{
v_t_4229_ = v_l_4234_;
goto _start;
}
case 1:
{
lean_inc(v_v_4233_);
return v_v_4233_;
}
default: 
{
v_t_4229_ = v_r_4235_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_4231_);
return v_fallback_4231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_4239_, lean_object* v_k_4240_, lean_object* v_fallback_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_4239_, v_k_4240_, v_fallback_4241_);
lean_dec(v_fallback_4241_);
lean_dec(v_k_4240_);
lean_dec(v_t_4239_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_4243_, size_t v_sz_4244_, size_t v_i_4245_, lean_object* v_b_4246_){
_start:
{
uint8_t v___x_4248_; 
v___x_4248_ = lean_usize_dec_lt(v_i_4245_, v_sz_4244_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4249_, 0, v_b_4246_);
return v___x_4249_;
}
else
{
lean_object* v_a_4250_; lean_object* v_fst_4251_; lean_object* v_snd_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; size_t v___x_4257_; size_t v___x_4258_; 
v_a_4250_ = lean_array_uget_borrowed(v_as_4243_, v_i_4245_);
v_fst_4251_ = lean_ctor_get(v_a_4250_, 0);
v_snd_4252_ = lean_ctor_get(v_a_4250_, 1);
v___x_4253_ = l_Lean_NameSet_empty;
v___x_4254_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_4246_, v_snd_4252_, v___x_4253_);
lean_inc(v_fst_4251_);
v___x_4255_ = l_Lean_NameSet_insert(v___x_4254_, v_fst_4251_);
lean_inc(v_snd_4252_);
v___x_4256_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_4252_, v___x_4255_, v_b_4246_);
v___x_4257_ = ((size_t)1ULL);
v___x_4258_ = lean_usize_add(v_i_4245_, v___x_4257_);
v_i_4245_ = v___x_4258_;
v_b_4246_ = v___x_4256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_4260_, lean_object* v_sz_4261_, lean_object* v_i_4262_, lean_object* v_b_4263_, lean_object* v___y_4264_){
_start:
{
size_t v_sz_boxed_4265_; size_t v_i_boxed_4266_; lean_object* v_res_4267_; 
v_sz_boxed_4265_ = lean_unbox_usize(v_sz_4261_);
lean_dec(v_sz_4261_);
v_i_boxed_4266_ = lean_unbox_usize(v_i_4262_);
lean_dec(v_i_4262_);
v_res_4267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4260_, v_sz_boxed_4265_, v_i_boxed_4266_, v_b_4263_);
lean_dec_ref(v_as_4260_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_4268_, size_t v_sz_4269_, size_t v_i_4270_, lean_object* v_b_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
uint8_t v___x_4275_; 
v___x_4275_ = lean_usize_dec_lt(v_i_4270_, v_sz_4269_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; 
v___x_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4276_, 0, v_b_4271_);
return v___x_4276_;
}
else
{
lean_object* v_a_4277_; size_t v_sz_4278_; size_t v___x_4279_; lean_object* v___x_4280_; 
v_a_4277_ = lean_array_uget_borrowed(v_as_4268_, v_i_4270_);
v_sz_4278_ = lean_array_size(v_a_4277_);
v___x_4279_ = ((size_t)0ULL);
v___x_4280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_4277_, v_sz_4278_, v___x_4279_, v_b_4271_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; size_t v___x_4282_; size_t v___x_4283_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v___x_4280_, 1);
v___x_4282_ = ((size_t)1ULL);
v___x_4283_ = lean_usize_add(v_i_4270_, v___x_4282_);
v_i_4270_ = v___x_4283_;
v_b_4271_ = v_a_4281_;
goto _start;
}
else
{
return v___x_4280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_4285_, lean_object* v_sz_4286_, lean_object* v_i_4287_, lean_object* v_b_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
size_t v_sz_boxed_4292_; size_t v_i_boxed_4293_; lean_object* v_res_4294_; 
v_sz_boxed_4292_ = lean_unbox_usize(v_sz_4286_);
lean_dec(v_sz_4286_);
v_i_boxed_4293_ = lean_unbox_usize(v_i_4287_);
lean_dec(v_i_4287_);
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_4285_, v_sz_boxed_4292_, v_i_boxed_4293_, v_b_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec_ref(v_as_4285_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_4295_, size_t v_i_4296_, size_t v_stop_4297_, lean_object* v_b_4298_){
_start:
{
uint8_t v___x_4299_; 
v___x_4299_ = lean_usize_dec_eq(v_i_4296_, v_stop_4297_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; lean_object* v_fst_4301_; lean_object* v_snd_4302_; lean_object* v___x_4303_; size_t v___x_4304_; size_t v___x_4305_; 
v___x_4300_ = lean_array_uget_borrowed(v_as_4295_, v_i_4296_);
v_fst_4301_ = lean_ctor_get(v___x_4300_, 0);
v_snd_4302_ = lean_ctor_get(v___x_4300_, 1);
lean_inc(v_snd_4302_);
lean_inc(v_fst_4301_);
v___x_4303_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4301_, v_snd_4302_, v_b_4298_);
v___x_4304_ = ((size_t)1ULL);
v___x_4305_ = lean_usize_add(v_i_4296_, v___x_4304_);
v_i_4296_ = v___x_4305_;
v_b_4298_ = v___x_4303_;
goto _start;
}
else
{
return v_b_4298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_4307_, lean_object* v_i_4308_, lean_object* v_stop_4309_, lean_object* v_b_4310_){
_start:
{
size_t v_i_boxed_4311_; size_t v_stop_boxed_4312_; lean_object* v_res_4313_; 
v_i_boxed_4311_ = lean_unbox_usize(v_i_4308_);
lean_dec(v_i_4308_);
v_stop_boxed_4312_ = lean_unbox_usize(v_stop_4309_);
lean_dec(v_stop_4309_);
v_res_4313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_4307_, v_i_boxed_4311_, v_stop_boxed_4312_, v_b_4310_);
lean_dec_ref(v_as_4307_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_4314_, size_t v_i_4315_, size_t v_stop_4316_, lean_object* v_b_4317_){
_start:
{
lean_object* v___y_4319_; uint8_t v___x_4323_; 
v___x_4323_ = lean_usize_dec_eq(v_i_4315_, v_stop_4316_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; 
v___x_4324_ = lean_array_uget_borrowed(v_as_4314_, v_i_4315_);
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = lean_array_get_size(v___x_4324_);
v___x_4327_ = lean_nat_dec_lt(v___x_4325_, v___x_4326_);
if (v___x_4327_ == 0)
{
v___y_4319_ = v_b_4317_;
goto v___jp_4318_;
}
else
{
size_t v___x_4328_; size_t v___x_4329_; lean_object* v___x_4330_; 
v___x_4328_ = ((size_t)0ULL);
v___x_4329_ = lean_usize_of_nat(v___x_4326_);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_4324_, v___x_4328_, v___x_4329_, v_b_4317_);
v___y_4319_ = v___x_4330_;
goto v___jp_4318_;
}
}
else
{
return v_b_4317_;
}
v___jp_4318_:
{
size_t v___x_4320_; size_t v___x_4321_; 
v___x_4320_ = ((size_t)1ULL);
v___x_4321_ = lean_usize_add(v_i_4315_, v___x_4320_);
v_i_4315_ = v___x_4321_;
v_b_4317_ = v___y_4319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_4331_, lean_object* v_i_4332_, lean_object* v_stop_4333_, lean_object* v_b_4334_){
_start:
{
size_t v_i_boxed_4335_; size_t v_stop_boxed_4336_; lean_object* v_res_4337_; 
v_i_boxed_4335_ = lean_unbox_usize(v_i_4332_);
lean_dec(v_i_4332_);
v_stop_boxed_4336_ = lean_unbox_usize(v_stop_4333_);
lean_dec(v_stop_4333_);
v_res_4337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_4331_, v_i_boxed_4335_, v_stop_boxed_4336_, v_b_4334_);
lean_dec_ref(v_as_4331_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_4338_){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v_env_4344_; lean_object* v___x_4345_; lean_object* v_ext_4346_; lean_object* v_toEnvExtension_4347_; lean_object* v_asyncMode_4348_; lean_object* v___x_4349_; lean_object* v_categories_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4340_ = lean_box(1);
v___x_4341_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4342_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4343_ = lean_st_ref_get(v___y_4338_);
v_env_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc_ref_n(v_env_4344_, 2);
lean_dec(v___x_4343_);
v___x_4345_ = l_Lean_Parser_parserExtension;
v_ext_4346_ = lean_ctor_get(v___x_4345_, 1);
v_toEnvExtension_4347_ = lean_ctor_get(v_ext_4346_, 0);
v_asyncMode_4348_ = lean_ctor_get(v_toEnvExtension_4347_, 2);
v___x_4349_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4342_, v___x_4345_, v_env_4344_, v_asyncMode_4348_);
v_categories_4350_ = lean_ctor_get(v___x_4349_, 2);
lean_inc_ref(v_categories_4350_);
lean_dec(v___x_4349_);
v___x_4351_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_4352_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_4350_, v___x_4351_);
lean_dec_ref(v_categories_4350_);
if (lean_obj_tag(v___x_4352_) == 1)
{
lean_object* v_val_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4384_; 
v_val_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4384_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_val_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4384_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___y_4358_; lean_object* v___x_4367_; lean_object* v_toEnvExtension_4368_; lean_object* v_exportEntriesFn_4369_; lean_object* v_asyncMode_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v_importedEntries_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v_exported_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4367_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_4368_ = lean_ctor_get(v___x_4367_, 0);
v_exportEntriesFn_4369_ = lean_ctor_get(v___x_4367_, 4);
v_asyncMode_4370_ = lean_ctor_get(v_toEnvExtension_4368_, 2);
v___x_4371_ = lean_box(0);
lean_inc_ref_n(v_env_4344_, 2);
v___x_4372_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4341_, v_toEnvExtension_4368_, v_env_4344_, v_asyncMode_4370_, v___x_4371_);
v_importedEntries_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc_ref(v_importedEntries_4373_);
lean_dec(v___x_4372_);
v___x_4374_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4340_, v___x_4367_, v_env_4344_, v_asyncMode_4370_, v___x_4371_);
lean_inc_ref(v_exportEntriesFn_4369_);
v___x_4375_ = lean_apply_2(v_exportEntriesFn_4369_, v_env_4344_, v___x_4374_);
v_exported_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_exported_4376_);
lean_dec_ref(v___x_4375_);
v___x_4377_ = lean_array_push(v_importedEntries_4373_, v_exported_4376_);
v___x_4378_ = lean_unsigned_to_nat(0u);
v___x_4379_ = lean_array_get_size(v___x_4377_);
v___x_4380_ = lean_nat_dec_lt(v___x_4378_, v___x_4379_);
if (v___x_4380_ == 0)
{
lean_dec_ref(v___x_4377_);
v___y_4358_ = v___x_4340_;
goto v___jp_4357_;
}
else
{
size_t v___x_4381_; size_t v___x_4382_; lean_object* v___x_4383_; 
v___x_4381_ = ((size_t)0ULL);
v___x_4382_ = lean_usize_of_nat(v___x_4379_);
v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_4377_, v___x_4381_, v___x_4382_, v___x_4340_);
lean_dec_ref(v___x_4377_);
v___y_4358_ = v___x_4383_;
goto v___jp_4357_;
}
v___jp_4357_:
{
lean_object* v_tables_4359_; lean_object* v_leadingTable_4360_; lean_object* v_trailingTable_4361_; lean_object* v_firstTokens_4362_; lean_object* v_firstTokens_4363_; lean_object* v___x_4365_; 
v_tables_4359_ = lean_ctor_get(v_val_4353_, 2);
v_leadingTable_4360_ = lean_ctor_get(v_tables_4359_, 0);
v_trailingTable_4361_ = lean_ctor_get(v_tables_4359_, 2);
lean_inc(v_trailingTable_4361_);
lean_inc(v_leadingTable_4360_);
lean_inc(v_val_4353_);
v_firstTokens_4362_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4353_, v_leadingTable_4360_, v___y_4358_);
v_firstTokens_4363_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_4353_, v_trailingTable_4361_, v_firstTokens_4362_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set_tag(v___x_4355_, 0);
lean_ctor_set(v___x_4355_, 0, v_firstTokens_4363_);
v___x_4365_ = v___x_4355_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_firstTokens_4363_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_object* v___x_4385_; 
lean_dec(v___x_4352_);
lean_dec_ref(v_env_4344_);
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4340_);
return v___x_4385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4386_);
lean_dec(v___y_4386_);
return v_res_4388_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0));
v___x_4391_ = l_Lean_stringToMessageData(v___x_4390_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v_env_4398_; lean_object* v___x_4399_; lean_object* v_env_4400_; lean_object* v___x_4401_; lean_object* v_env_4402_; lean_object* v___x_4403_; lean_object* v_toEnvExtension_4404_; lean_object* v_exportEntriesFn_4405_; lean_object* v_asyncMode_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v_importedEntries_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4461_; 
v___x_4395_ = lean_box(1);
v___x_4396_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_4397_ = lean_st_ref_get(v_a_4393_);
v_env_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc_ref(v_env_4398_);
lean_dec(v___x_4397_);
v___x_4399_ = lean_st_ref_get(v_a_4393_);
v_env_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc_ref(v_env_4400_);
lean_dec(v___x_4399_);
v___x_4401_ = lean_st_ref_get(v_a_4393_);
v_env_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc_ref(v_env_4402_);
lean_dec(v___x_4401_);
v___x_4403_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_4404_ = lean_ctor_get(v___x_4403_, 0);
v_exportEntriesFn_4405_ = lean_ctor_get(v___x_4403_, 4);
v_asyncMode_4406_ = lean_ctor_get(v_toEnvExtension_4404_, 2);
v___x_4407_ = lean_box(0);
v___x_4408_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4396_, v_toEnvExtension_4404_, v_env_4398_, v_asyncMode_4406_, v___x_4407_);
v_importedEntries_4409_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4461_ == 0)
{
lean_object* v_unused_4462_; 
v_unused_4462_ = lean_ctor_get(v___x_4408_, 1);
lean_dec(v_unused_4462_);
v___x_4411_ = v___x_4408_;
v_isShared_4412_ = v_isSharedCheck_4461_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_importedEntries_4409_);
lean_dec(v___x_4408_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4461_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v_exported_4415_; lean_object* v___x_4416_; size_t v_sz_4417_; size_t v___x_4418_; lean_object* v___x_4419_; 
v___x_4413_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4395_, v___x_4403_, v_env_4402_, v_asyncMode_4406_, v___x_4407_);
lean_inc_ref(v_exportEntriesFn_4405_);
v___x_4414_ = lean_apply_2(v_exportEntriesFn_4405_, v_env_4400_, v___x_4413_);
v_exported_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_exported_4415_);
lean_dec_ref(v___x_4414_);
v___x_4416_ = lean_array_push(v_importedEntries_4409_, v_exported_4415_);
v_sz_4417_ = lean_array_size(v___x_4416_);
v___x_4418_ = ((size_t)0ULL);
v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_4416_, v_sz_4417_, v___x_4418_, v___x_4395_, v_a_4392_, v_a_4393_);
lean_dec_ref(v___x_4416_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4421_; lean_object* v_a_4422_; lean_object* v___x_4423_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v___x_4421_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_4393_);
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref(v___x_4421_);
v___x_4423_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_4392_, v_a_4393_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
lean_dec_ref_known(v___x_4423_, 1);
v___x_4425_ = lean_box(0);
v___x_4426_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_4422_, v_a_4420_, v_a_4424_, v___x_4425_, v_a_4392_, v_a_4393_);
lean_dec(v_a_4420_);
lean_dec(v_a_4422_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4432_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4426_, 1);
v___x_4428_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1);
v___x_4429_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_parseVersoDocString___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_docCommentMarkdown_spec__1_spec__3_spec__5_spec__11___closed__0);
v___x_4430_ = l_Lean_MessageData_joinSep(v_a_4427_, v___x_4429_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 7);
lean_ctor_set(v___x_4411_, 1, v___x_4430_);
lean_ctor_set(v___x_4411_, 0, v___x_4429_);
v___x_4432_ = v___x_4411_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4429_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v___x_4430_);
v___x_4432_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4433_ = l_Lean_MessageData_nestD(v___x_4432_);
v___x_4434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4428_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
v___x_4435_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_4434_, v_a_4392_, v_a_4393_);
return v___x_4435_;
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_del_object(v___x_4411_);
v_a_4437_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4426_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4426_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_a_4422_);
lean_dec(v_a_4420_);
lean_del_object(v___x_4411_);
v_a_4445_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4423_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4423_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_del_object(v___x_4411_);
v_a_4453_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4419_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4419_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4463_, v_a_4464_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_4468_, v_a_4469_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_4472_, v_a_4473_, v_a_4474_);
lean_dec(v_a_4474_);
lean_dec_ref(v_a_4473_);
lean_dec(v___stx_4472_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_4477_, lean_object* v_t_4478_, lean_object* v_k_4479_, lean_object* v_fallback_4480_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_4478_, v_k_4479_, v_fallback_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_4482_, lean_object* v_t_4483_, lean_object* v_k_4484_, lean_object* v_fallback_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_4482_, v_t_4483_, v_k_4484_, v_fallback_4485_);
lean_dec(v_fallback_4485_);
lean_dec(v_k_4484_);
lean_dec(v_t_4483_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_4487_, size_t v_sz_4488_, size_t v_i_4489_, lean_object* v_b_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_4487_, v_sz_4488_, v_i_4489_, v_b_4490_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_4495_, lean_object* v_sz_4496_, lean_object* v_i_4497_, lean_object* v_b_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
size_t v_sz_boxed_4502_; size_t v_i_boxed_4503_; lean_object* v_res_4504_; 
v_sz_boxed_4502_ = lean_unbox_usize(v_sz_4496_);
lean_dec(v_sz_4496_);
v_i_boxed_4503_ = lean_unbox_usize(v_i_4497_);
lean_dec(v_i_4497_);
v_res_4504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_4495_, v_sz_boxed_4502_, v_i_boxed_4503_, v_b_4498_, v___y_4499_, v___y_4500_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec_ref(v_as_4495_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_4513_, lean_object* v___x_4514_, lean_object* v___x_4515_, lean_object* v_inst_4516_, lean_object* v_R_4517_, lean_object* v_a_4518_, lean_object* v_b_4519_){
_start:
{
lean_object* v___x_4520_; 
v___x_4520_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_4513_, v___x_4514_, v___x_4515_, v_a_4518_, v_b_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_4521_, lean_object* v___x_4522_, lean_object* v___x_4523_, lean_object* v_inst_4524_, lean_object* v_R_4525_, lean_object* v_a_4526_, lean_object* v_b_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_4521_, v___x_4522_, v___x_4523_, v_inst_4524_, v_R_4525_, v_a_4526_, v_b_4527_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v_val_4521_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_4529_, lean_object* v_t_4530_){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_4529_, v_t_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_4532_, lean_object* v_as_4533_, lean_object* v_lo_4534_, lean_object* v_hi_4535_, lean_object* v_w_4536_, lean_object* v_hlo_4537_, lean_object* v_hhi_4538_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_4532_, v_as_4533_, v_lo_4534_, v_hi_4535_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_4540_, lean_object* v_as_4541_, lean_object* v_lo_4542_, lean_object* v_hi_4543_, lean_object* v_w_4544_, lean_object* v_hlo_4545_, lean_object* v_hhi_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_4540_, v_as_4541_, v_lo_4542_, v_hi_4543_, v_w_4544_, v_hlo_4545_, v_hhi_4546_);
lean_dec(v_hi_4543_);
lean_dec(v_n_4540_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_4548_, lean_object* v_x_4549_, lean_object* v_x_4550_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_4549_, v_x_4550_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_4552_, lean_object* v_x_4553_, lean_object* v_x_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_4552_, v_x_4553_, v_x_4554_);
lean_dec(v_x_4554_);
lean_dec_ref(v_x_4553_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___x_4560_; 
v___x_4560_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_4556_, v___y_4558_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_4561_, v___y_4562_, v___y_4563_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_4566_, lean_object* v_t_4567_, lean_object* v_k_4568_){
_start:
{
lean_object* v___x_4569_; 
v___x_4569_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_4567_, v_k_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_4570_, lean_object* v_t_4571_, lean_object* v_k_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_4570_, v_t_4571_, v_k_4572_);
lean_dec(v_k_4572_);
lean_dec(v_t_4571_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_4574_, lean_object* v_x_4575_, lean_object* v_x_4576_){
_start:
{
lean_object* v___x_4577_; 
v___x_4577_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_4575_, v_x_4576_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_4578_, lean_object* v_x_4579_, lean_object* v_x_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_4578_, v_x_4579_, v_x_4580_);
lean_dec(v_x_4580_);
lean_dec_ref(v_x_4579_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_4582_, lean_object* v_lo_4583_, lean_object* v_hi_4584_, lean_object* v_hhi_4585_, lean_object* v_pivot_4586_, lean_object* v_as_4587_, lean_object* v_i_4588_, lean_object* v_k_4589_, lean_object* v_ilo_4590_, lean_object* v_ik_4591_, lean_object* v_w_4592_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_4584_, v_pivot_4586_, v_as_4587_, v_i_4588_, v_k_4589_);
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_4594_, lean_object* v_lo_4595_, lean_object* v_hi_4596_, lean_object* v_hhi_4597_, lean_object* v_pivot_4598_, lean_object* v_as_4599_, lean_object* v_i_4600_, lean_object* v_k_4601_, lean_object* v_ilo_4602_, lean_object* v_ik_4603_, lean_object* v_w_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_4594_, v_lo_4595_, v_hi_4596_, v_hhi_4597_, v_pivot_4598_, v_as_4599_, v_i_4600_, v_k_4601_, v_ilo_4602_, v_ik_4603_, v_w_4604_);
lean_dec(v_hi_4596_);
lean_dec(v_lo_4595_);
lean_dec(v_n_4594_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_4606_, size_t v_sz_4607_, size_t v_i_4608_, lean_object* v_b_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_4606_, v_sz_4607_, v_i_4608_, v_b_4609_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_4614_, lean_object* v_sz_4615_, lean_object* v_i_4616_, lean_object* v_b_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
size_t v_sz_boxed_4621_; size_t v_i_boxed_4622_; lean_object* v_res_4623_; 
v_sz_boxed_4621_ = lean_unbox_usize(v_sz_4615_);
lean_dec(v_sz_4615_);
v_i_boxed_4622_ = lean_unbox_usize(v_i_4616_);
lean_dec(v_i_4616_);
v_res_4623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_4614_, v_sz_boxed_4621_, v_i_boxed_4622_, v_b_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec_ref(v_as_4614_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_4624_, lean_object* v_t_4625_){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_4624_, v_t_4625_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_4627_, lean_object* v_t_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_4627_, v_t_4628_);
lean_dec(v_t_4628_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_4630_, lean_object* v_as_4631_, lean_object* v_lo_4632_, lean_object* v_hi_4633_, lean_object* v_w_4634_, lean_object* v_hlo_4635_, lean_object* v_hhi_4636_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_4630_, v_as_4631_, v_lo_4632_, v_hi_4633_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_4638_, lean_object* v_as_4639_, lean_object* v_lo_4640_, lean_object* v_hi_4641_, lean_object* v_w_4642_, lean_object* v_hlo_4643_, lean_object* v_hhi_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_4638_, v_as_4639_, v_lo_4640_, v_hi_4641_, v_w_4642_, v_hlo_4643_, v_hhi_4644_);
lean_dec(v_hi_4641_);
lean_dec(v_n_4638_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_4646_, lean_object* v_x_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_4646_, v_x_4647_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_4652_, lean_object* v_x_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_4652_, v_x_4653_, v___y_4654_, v___y_4655_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_4658_, lean_object* v_x_4659_, size_t v_x_4660_, lean_object* v_x_4661_){
_start:
{
lean_object* v___x_4662_; 
v___x_4662_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_4659_, v_x_4660_, v_x_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_4663_, lean_object* v_x_4664_, lean_object* v_x_4665_, lean_object* v_x_4666_){
_start:
{
size_t v_x_18971__boxed_4667_; lean_object* v_res_4668_; 
v_x_18971__boxed_4667_ = lean_unbox_usize(v_x_4665_);
lean_dec(v_x_4665_);
v_res_4668_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_4663_, v_x_4664_, v_x_18971__boxed_4667_, v_x_4666_);
lean_dec(v_x_4666_);
lean_dec_ref(v_x_4664_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_4669_, lean_object* v_k_4670_, lean_object* v_x_4671_, lean_object* v_x_4672_, lean_object* v_x_4673_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_4669_, v_k_4670_, v_x_4671_, v_x_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_4675_, lean_object* v_k_4676_, lean_object* v_x_4677_, lean_object* v_x_4678_, lean_object* v_x_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_4675_, v_k_4676_, v_x_4677_, v_x_4678_, v_x_4679_);
lean_dec_ref(v_k_4676_);
lean_dec_ref(v_as_4675_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_4681_, lean_object* v_m_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v___x_4684_; 
v___x_4684_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_4682_, v_a_4683_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_4685_, lean_object* v_m_4686_, lean_object* v_a_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_4685_, v_m_4686_, v_a_4687_);
lean_dec(v_a_4687_);
lean_dec_ref(v_m_4686_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_4689_, lean_object* v_lo_4690_, lean_object* v_hi_4691_, lean_object* v_hhi_4692_, lean_object* v_pivot_4693_, lean_object* v_as_4694_, lean_object* v_i_4695_, lean_object* v_k_4696_, lean_object* v_ilo_4697_, lean_object* v_ik_4698_, lean_object* v_w_4699_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_4691_, v_pivot_4693_, v_as_4694_, v_i_4695_, v_k_4696_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_4701_, lean_object* v_lo_4702_, lean_object* v_hi_4703_, lean_object* v_hhi_4704_, lean_object* v_pivot_4705_, lean_object* v_as_4706_, lean_object* v_i_4707_, lean_object* v_k_4708_, lean_object* v_ilo_4709_, lean_object* v_ik_4710_, lean_object* v_w_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_4701_, v_lo_4702_, v_hi_4703_, v_hhi_4704_, v_pivot_4705_, v_as_4706_, v_i_4707_, v_k_4708_, v_ilo_4709_, v_ik_4710_, v_w_4711_);
lean_dec(v_hi_4703_);
lean_dec(v_lo_4702_);
lean_dec(v_n_4701_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_4713_, lean_object* v_keys_4714_, lean_object* v_vals_4715_, lean_object* v_heq_4716_, lean_object* v_i_4717_, lean_object* v_k_4718_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_4714_, v_vals_4715_, v_i_4717_, v_k_4718_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_4720_, lean_object* v_keys_4721_, lean_object* v_vals_4722_, lean_object* v_heq_4723_, lean_object* v_i_4724_, lean_object* v_k_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_4720_, v_keys_4721_, v_vals_4722_, v_heq_4723_, v_i_4724_, v_k_4725_);
lean_dec(v_k_4725_);
lean_dec_ref(v_vals_4722_);
lean_dec_ref(v_keys_4721_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_4727_, lean_object* v_a_4728_, lean_object* v_x_4729_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_4728_, v_x_4729_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_4731_, lean_object* v_a_4732_, lean_object* v_x_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_4731_, v_a_4732_, v_x_4733_);
lean_dec(v_x_4733_);
lean_dec(v_a_4732_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4749_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_4751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4752_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_4753_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4749_, v___x_4750_, v___x_4751_, v___x_4752_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_4760_ = l_Lean_addBuiltinDocString(v___x_4758_, v___x_4759_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_4790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_4791_ = l_Lean_addBuiltinDeclarationRanges(v___x_4789_, v___x_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_4793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_4794_, lean_object* v___x_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, uint8_t v_includeUnnamed_4798_, lean_object* v_x_4799_, lean_object* v_____s_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v_fst_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4861_; 
v_fst_4806_ = lean_ctor_get(v_x_4799_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v_x_4799_);
if (v_isSharedCheck_4861_ == 0)
{
lean_object* v_unused_4862_; 
v_unused_4862_ = lean_ctor_get(v_x_4799_, 1);
lean_dec(v_unused_4862_);
v___x_4808_ = v_x_4799_;
v_isShared_4809_ = v_isSharedCheck_4861_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_fst_4806_);
lean_dec(v_x_4799_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4861_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v_userName_4811_; lean_object* v___y_4812_; lean_object* v___x_4846_; 
lean_inc(v_fst_4806_);
lean_inc_ref(v_env_4794_);
v___x_4846_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_4794_, v_fst_4806_);
if (lean_obj_tag(v___x_4846_) == 1)
{
lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4854_; 
lean_del_object(v___x_4808_);
lean_dec(v_fst_4806_);
lean_dec(v___x_4795_);
lean_dec_ref(v_env_4794_);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4854_ == 0)
{
lean_object* v_unused_4855_; 
v_unused_4855_ = lean_ctor_get(v___x_4846_, 0);
lean_dec(v_unused_4855_);
v___x_4848_ = v___x_4846_;
v_isShared_4849_ = v_isSharedCheck_4854_;
goto v_resetjp_4847_;
}
else
{
lean_dec(v___x_4846_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4854_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 0, v_____s_4800_);
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_____s_4800_);
v___x_4851_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
lean_object* v___x_4852_; 
v___x_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4851_);
return v___x_4852_;
}
}
}
else
{
lean_object* v___x_4856_; 
lean_dec(v___x_4846_);
v___x_4856_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_4797_, v_fst_4806_);
if (lean_obj_tag(v___x_4856_) == 1)
{
lean_object* v_val_4857_; 
v_val_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc(v_val_4857_);
lean_dec_ref_known(v___x_4856_, 1);
v_userName_4811_ = v_val_4857_;
v___y_4812_ = v___y_4803_;
goto v___jp_4810_;
}
else
{
lean_dec(v___x_4856_);
if (v_includeUnnamed_4798_ == 0)
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
lean_del_object(v___x_4808_);
lean_dec(v_fst_4806_);
lean_dec(v___x_4795_);
lean_dec_ref(v_env_4794_);
v___x_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4858_, 0, v_____s_4800_);
v___x_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
return v___x_4859_;
}
else
{
lean_object* v___x_4860_; 
lean_inc(v_fst_4806_);
v___x_4860_ = l_Lean_Name_toString(v_fst_4806_, v_includeUnnamed_4798_);
v_userName_4811_ = v___x_4860_;
v___y_4812_ = v___y_4803_;
goto v___jp_4810_;
}
}
}
v___jp_4810_:
{
lean_object* v_ref_4813_; uint8_t v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v_ref_4813_ = lean_ctor_get(v___y_4812_, 2);
v___x_4814_ = 1;
v___x_4815_ = l_Lean_Options_empty;
v___x_4816_ = lean_box(0);
lean_inc(v_fst_4806_);
lean_inc_ref(v_env_4794_);
v___x_4817_ = l_Lean_findDocString_x3f(v_env_4794_, v_fst_4806_, v___x_4814_, v___x_4815_, v___x_4795_, v___x_4816_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4831_; 
lean_del_object(v___x_4808_);
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4831_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4831_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4822_ = l_Lean_NameSet_empty;
v___x_4823_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_4796_, v_fst_4806_, v___x_4822_);
lean_inc(v_fst_4806_);
v___x_4824_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_4794_, v_fst_4806_);
v___x_4825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4825_, 0, v_fst_4806_);
lean_ctor_set(v___x_4825_, 1, v_userName_4811_);
lean_ctor_set(v___x_4825_, 2, v___x_4823_);
lean_ctor_set(v___x_4825_, 3, v_a_4818_);
lean_ctor_set(v___x_4825_, 4, v___x_4824_);
v___x_4826_ = lean_array_push(v_____s_4800_, v___x_4825_);
v___x_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v___x_4827_);
v___x_4829_ = v___x_4820_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4845_; 
lean_dec_ref(v_userName_4811_);
lean_dec(v_fst_4806_);
lean_dec_ref(v_____s_4800_);
lean_dec_ref(v_env_4794_);
v_a_4832_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4834_ = v___x_4817_;
v_isShared_4835_ = v_isSharedCheck_4845_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4817_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4845_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4840_; 
v___x_4836_ = lean_io_error_to_string(v_a_4832_);
v___x_4837_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
v___x_4838_ = l_Lean_MessageData_ofFormat(v___x_4837_);
lean_inc(v_ref_4813_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 1, v___x_4838_);
lean_ctor_set(v___x_4808_, 0, v_ref_4813_);
v___x_4840_ = v___x_4808_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_ref_4813_);
lean_ctor_set(v_reuseFailAlloc_4844_, 1, v___x_4838_);
v___x_4840_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
lean_object* v___x_4842_; 
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 0, v___x_4840_);
v___x_4842_ = v___x_4834_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4840_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_4863_, lean_object* v___x_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_includeUnnamed_4867_, lean_object* v_x_4868_, lean_object* v_____s_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
uint8_t v_includeUnnamed_boxed_4875_; lean_object* v_res_4876_; 
v_includeUnnamed_boxed_4875_ = lean_unbox(v_includeUnnamed_4867_);
v_res_4876_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_4863_, v___x_4864_, v_a_4865_, v_a_4866_, v_includeUnnamed_boxed_4875_, v_x_4868_, v_____s_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v_a_4866_);
lean_dec(v_a_4865_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_4877_, size_t v_sz_4878_, size_t v_i_4879_, lean_object* v_b_4880_){
_start:
{
uint8_t v___x_4882_; 
v___x_4882_ = lean_usize_dec_lt(v_i_4879_, v_sz_4878_);
if (v___x_4882_ == 0)
{
lean_object* v___x_4883_; 
v___x_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4883_, 0, v_b_4880_);
return v___x_4883_;
}
else
{
lean_object* v_a_4884_; lean_object* v_fst_4885_; lean_object* v_snd_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; size_t v___x_4891_; size_t v___x_4892_; 
v_a_4884_ = lean_array_uget_borrowed(v_as_4877_, v_i_4879_);
v_fst_4885_ = lean_ctor_get(v_a_4884_, 0);
v_snd_4886_ = lean_ctor_get(v_a_4884_, 1);
v___x_4887_ = l_Lean_NameSet_empty;
v___x_4888_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_4880_, v_fst_4885_, v___x_4887_);
lean_inc(v_snd_4886_);
v___x_4889_ = l_Lean_NameSet_insert(v___x_4888_, v_snd_4886_);
lean_inc(v_fst_4885_);
v___x_4890_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4885_, v___x_4889_, v_b_4880_);
v___x_4891_ = ((size_t)1ULL);
v___x_4892_ = lean_usize_add(v_i_4879_, v___x_4891_);
v_i_4879_ = v___x_4892_;
v_b_4880_ = v___x_4890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_4894_, lean_object* v_sz_4895_, lean_object* v_i_4896_, lean_object* v_b_4897_, lean_object* v___y_4898_){
_start:
{
size_t v_sz_boxed_4899_; size_t v_i_boxed_4900_; lean_object* v_res_4901_; 
v_sz_boxed_4899_ = lean_unbox_usize(v_sz_4895_);
lean_dec(v_sz_4895_);
v_i_boxed_4900_ = lean_unbox_usize(v_i_4896_);
lean_dec(v_i_4896_);
v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4894_, v_sz_boxed_4899_, v_i_boxed_4900_, v_b_4897_);
lean_dec_ref(v_as_4894_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_4902_, size_t v_sz_4903_, size_t v_i_4904_, lean_object* v_b_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
uint8_t v___x_4911_; 
v___x_4911_ = lean_usize_dec_lt(v_i_4904_, v_sz_4903_);
if (v___x_4911_ == 0)
{
lean_object* v___x_4912_; 
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v_b_4905_);
return v___x_4912_;
}
else
{
lean_object* v_a_4913_; size_t v_sz_4914_; size_t v___x_4915_; lean_object* v___x_4916_; 
v_a_4913_ = lean_array_uget_borrowed(v_as_4902_, v_i_4904_);
v_sz_4914_ = lean_array_size(v_a_4913_);
v___x_4915_ = ((size_t)0ULL);
v___x_4916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_4913_, v_sz_4914_, v___x_4915_, v_b_4905_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; size_t v___x_4918_; size_t v___x_4919_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
lean_inc(v_a_4917_);
lean_dec_ref_known(v___x_4916_, 1);
v___x_4918_ = ((size_t)1ULL);
v___x_4919_ = lean_usize_add(v_i_4904_, v___x_4918_);
v_i_4904_ = v___x_4919_;
v_b_4905_ = v_a_4917_;
goto _start;
}
else
{
return v___x_4916_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_4921_, lean_object* v_sz_4922_, lean_object* v_i_4923_, lean_object* v_b_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
size_t v_sz_boxed_4930_; size_t v_i_boxed_4931_; lean_object* v_res_4932_; 
v_sz_boxed_4930_ = lean_unbox_usize(v_sz_4922_);
lean_dec(v_sz_4922_);
v_i_boxed_4931_ = lean_unbox_usize(v_i_4923_);
lean_dec(v_i_4923_);
v_res_4932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_4921_, v_sz_boxed_4930_, v_i_boxed_4931_, v_b_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec_ref(v_as_4921_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_4933_, lean_object* v_keys_4934_, lean_object* v_vals_4935_, lean_object* v_i_4936_, lean_object* v_acc_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_){
_start:
{
lean_object* v___x_4943_; uint8_t v___x_4944_; 
v___x_4943_ = lean_array_get_size(v_keys_4934_);
v___x_4944_ = lean_nat_dec_lt(v_i_4936_, v___x_4943_);
if (v___x_4944_ == 0)
{
lean_object* v___x_4945_; lean_object* v___x_4946_; 
lean_dec(v_i_4936_);
lean_dec_ref(v_f_4933_);
v___x_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4945_, 0, v_acc_4937_);
v___x_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4945_);
return v___x_4946_;
}
else
{
lean_object* v_k_4947_; lean_object* v_v_4948_; lean_object* v___x_4949_; 
v_k_4947_ = lean_array_fget_borrowed(v_keys_4934_, v_i_4936_);
v_v_4948_ = lean_array_fget_borrowed(v_vals_4935_, v_i_4936_);
lean_inc_ref(v_f_4933_);
lean_inc(v___y_4941_);
lean_inc_ref(v___y_4940_);
lean_inc(v___y_4939_);
lean_inc_ref(v___y_4938_);
lean_inc(v_v_4948_);
lean_inc(v_k_4947_);
v___x_4949_ = lean_apply_8(v_f_4933_, v_acc_4937_, v_k_4947_, v_v_4948_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, lean_box(0));
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_a_4950_);
if (lean_obj_tag(v_a_4950_) == 0)
{
lean_dec_ref_known(v_a_4950_, 1);
lean_dec(v_i_4936_);
lean_dec_ref(v_f_4933_);
return v___x_4949_;
}
else
{
lean_object* v_a_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_dec_ref_known(v___x_4949_, 1);
v_a_4951_ = lean_ctor_get(v_a_4950_, 0);
lean_inc(v_a_4951_);
lean_dec_ref_known(v_a_4950_, 1);
v___x_4952_ = lean_unsigned_to_nat(1u);
v___x_4953_ = lean_nat_add(v_i_4936_, v___x_4952_);
lean_dec(v_i_4936_);
v_i_4936_ = v___x_4953_;
v_acc_4937_ = v_a_4951_;
goto _start;
}
}
else
{
lean_dec(v_i_4936_);
lean_dec_ref(v_f_4933_);
return v___x_4949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_4955_, lean_object* v_keys_4956_, lean_object* v_vals_4957_, lean_object* v_i_4958_, lean_object* v_acc_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4955_, v_keys_4956_, v_vals_4957_, v_i_4958_, v_acc_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec_ref(v_vals_4957_);
lean_dec_ref(v_keys_4956_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_4966_, lean_object* v_as_4967_, size_t v_i_4968_, size_t v_stop_4969_, lean_object* v_b_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v_a_4977_; lean_object* v___y_4982_; uint8_t v___x_4985_; 
v___x_4985_ = lean_usize_dec_eq(v_i_4968_, v_stop_4969_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
v___x_4986_ = lean_array_uget_borrowed(v_as_4967_, v_i_4968_);
switch(lean_obj_tag(v___x_4986_))
{
case 0:
{
lean_object* v_key_4987_; lean_object* v_val_4988_; lean_object* v___x_4989_; 
v_key_4987_ = lean_ctor_get(v___x_4986_, 0);
v_val_4988_ = lean_ctor_get(v___x_4986_, 1);
lean_inc_ref(v_f_4966_);
lean_inc(v___y_4974_);
lean_inc_ref(v___y_4973_);
lean_inc(v___y_4972_);
lean_inc_ref(v___y_4971_);
lean_inc(v_val_4988_);
lean_inc(v_key_4987_);
v___x_4989_ = lean_apply_8(v_f_4966_, v_b_4970_, v_key_4987_, v_val_4988_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, lean_box(0));
v___y_4982_ = v___x_4989_;
goto v___jp_4981_;
}
case 1:
{
lean_object* v_node_4990_; lean_object* v___x_4991_; 
v_node_4990_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_node_4990_);
lean_inc_ref(v_f_4966_);
v___x_4991_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4966_, v_node_4990_, v_b_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
v___y_4982_ = v___x_4991_;
goto v___jp_4981_;
}
default: 
{
v_a_4977_ = v_b_4970_;
goto v___jp_4976_;
}
}
}
else
{
lean_object* v___x_4992_; lean_object* v___x_4993_; 
lean_dec_ref(v_f_4966_);
v___x_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4992_, 0, v_b_4970_);
v___x_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
return v___x_4993_;
}
v___jp_4976_:
{
size_t v___x_4978_; size_t v___x_4979_; 
v___x_4978_ = ((size_t)1ULL);
v___x_4979_ = lean_usize_add(v_i_4968_, v___x_4978_);
v_i_4968_ = v___x_4979_;
v_b_4970_ = v_a_4977_;
goto _start;
}
v___jp_4981_:
{
if (lean_obj_tag(v___y_4982_) == 0)
{
lean_object* v_a_4983_; 
v_a_4983_ = lean_ctor_get(v___y_4982_, 0);
if (lean_obj_tag(v_a_4983_) == 0)
{
lean_dec_ref(v_f_4966_);
return v___y_4982_;
}
else
{
lean_object* v_a_4984_; 
lean_inc_ref(v_a_4983_);
lean_dec_ref_known(v___y_4982_, 1);
v_a_4984_ = lean_ctor_get(v_a_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v_a_4983_, 1);
v_a_4977_ = v_a_4984_;
goto v___jp_4976_;
}
}
else
{
lean_dec_ref(v_f_4966_);
return v___y_4982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_4994_, lean_object* v_x_4995_, lean_object* v_x_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
if (lean_obj_tag(v_x_4995_) == 0)
{
lean_object* v_es_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5016_; 
v_es_5002_ = lean_ctor_get(v_x_4995_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v_x_4995_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5004_ = v_x_4995_;
v_isShared_5005_ = v_isSharedCheck_5016_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_es_5002_);
lean_dec(v_x_4995_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5016_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; uint8_t v___x_5008_; 
v___x_5006_ = lean_unsigned_to_nat(0u);
v___x_5007_ = lean_array_get_size(v_es_5002_);
v___x_5008_ = lean_nat_dec_lt(v___x_5006_, v___x_5007_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5010_; 
lean_dec_ref(v_es_5002_);
lean_dec_ref(v_f_4994_);
if (v_isShared_5005_ == 0)
{
lean_ctor_set_tag(v___x_5004_, 1);
lean_ctor_set(v___x_5004_, 0, v_x_4996_);
v___x_5010_ = v___x_5004_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_x_4996_);
v___x_5010_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
lean_object* v___x_5011_; 
v___x_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5011_, 0, v___x_5010_);
return v___x_5011_;
}
}
else
{
size_t v___x_5013_; size_t v___x_5014_; lean_object* v___x_5015_; 
lean_del_object(v___x_5004_);
v___x_5013_ = ((size_t)0ULL);
v___x_5014_ = lean_usize_of_nat(v___x_5007_);
v___x_5015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4994_, v_es_5002_, v___x_5013_, v___x_5014_, v_x_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
lean_dec_ref(v_es_5002_);
return v___x_5015_;
}
}
}
else
{
lean_object* v_ks_5017_; lean_object* v_vs_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v_ks_5017_ = lean_ctor_get(v_x_4995_, 0);
lean_inc_ref(v_ks_5017_);
v_vs_5018_ = lean_ctor_get(v_x_4995_, 1);
lean_inc_ref(v_vs_5018_);
lean_dec_ref_known(v_x_4995_, 2);
v___x_5019_ = lean_unsigned_to_nat(0u);
v___x_5020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4994_, v_ks_5017_, v_vs_5018_, v___x_5019_, v_x_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
lean_dec_ref(v_vs_5018_);
lean_dec_ref(v_ks_5017_);
return v___x_5020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_5021_, lean_object* v_x_5022_, lean_object* v_x_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5021_, v_x_5022_, v_x_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_);
lean_dec(v___y_5027_);
lean_dec_ref(v___y_5026_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
return v_res_5029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_5030_, lean_object* v_as_5031_, lean_object* v_i_5032_, lean_object* v_stop_5033_, lean_object* v_b_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_){
_start:
{
size_t v_i_boxed_5040_; size_t v_stop_boxed_5041_; lean_object* v_res_5042_; 
v_i_boxed_5040_ = lean_unbox_usize(v_i_5032_);
lean_dec(v_i_5032_);
v_stop_boxed_5041_ = lean_unbox_usize(v_stop_5033_);
lean_dec(v_stop_5033_);
v_res_5042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_5030_, v_as_5031_, v_i_boxed_5040_, v_stop_boxed_5041_, v_b_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
lean_dec(v___y_5038_);
lean_dec_ref(v___y_5037_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
lean_dec_ref(v_as_5031_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_5043_, lean_object* v_s_5044_, lean_object* v_a_5045_, lean_object* v_b_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5052_, 0, v_a_5045_);
lean_ctor_set(v___x_5052_, 1, v_b_5046_);
lean_inc(v___y_5050_);
lean_inc_ref(v___y_5049_);
lean_inc(v___y_5048_);
lean_inc_ref(v___y_5047_);
v___x_5053_ = lean_apply_7(v_f_5043_, v___x_5052_, v_s_5044_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, lean_box(0));
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5080_; 
v_a_5054_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5056_ = v___x_5053_;
v_isShared_5057_ = v_isSharedCheck_5080_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5053_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5080_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
if (lean_obj_tag(v_a_5054_) == 0)
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5068_; 
v_a_5058_ = lean_ctor_get(v_a_5054_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v_a_5054_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5060_ = v_a_5054_;
v_isShared_5061_ = v_isSharedCheck_5068_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v_a_5054_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5068_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
lean_object* v___x_5065_; 
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 0, v___x_5063_);
v___x_5065_ = v___x_5056_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v___x_5063_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5079_; 
v_a_5069_ = lean_ctor_get(v_a_5054_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v_a_5054_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5071_ = v_a_5054_;
v_isShared_5072_ = v_isSharedCheck_5079_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v_a_5054_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5079_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5076_; 
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 0, v___x_5074_);
v___x_5076_ = v___x_5056_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5074_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
v_a_5081_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5053_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5053_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_5089_, lean_object* v_s_5090_, lean_object* v_a_5091_, lean_object* v_b_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_5089_, v_s_5090_, v_a_5091_, v_b_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
lean_dec(v___y_5094_);
lean_dec_ref(v___y_5093_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_5099_, lean_object* v_init_5100_, lean_object* v_f_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_){
_start:
{
lean_object* v___f_5107_; lean_object* v___x_5108_; 
v___f_5107_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5107_, 0, v_f_5101_);
lean_inc_ref(v_map_5099_);
v___x_5108_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_5107_, v_map_5099_, v_init_5100_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5117_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5108_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5111_ = v___x_5108_;
v_isShared_5112_ = v_isSharedCheck_5117_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5108_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5117_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v_a_5113_; lean_object* v___x_5115_; 
v_a_5113_ = lean_ctor_get(v_a_5109_, 0);
lean_inc(v_a_5113_);
lean_dec(v_a_5109_);
if (v_isShared_5112_ == 0)
{
lean_ctor_set(v___x_5111_, 0, v_a_5113_);
v___x_5115_ = v___x_5111_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5113_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
else
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5125_; 
v_a_5118_ = lean_ctor_get(v___x_5108_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5108_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5108_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5108_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5123_; 
if (v_isShared_5121_ == 0)
{
v___x_5123_ = v___x_5120_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_5126_, lean_object* v_init_5127_, lean_object* v_f_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_5126_, v_init_5127_, v_f_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec_ref(v_map_5126_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_5135_){
_start:
{
lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v_env_5141_; lean_object* v___x_5142_; lean_object* v_ext_5143_; lean_object* v_toEnvExtension_5144_; lean_object* v_asyncMode_5145_; lean_object* v___x_5146_; lean_object* v_categories_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5137_ = lean_box(1);
v___x_5138_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_5139_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_5140_ = lean_st_ref_get(v___y_5135_);
v_env_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc_ref_n(v_env_5141_, 2);
lean_dec(v___x_5140_);
v___x_5142_ = l_Lean_Parser_parserExtension;
v_ext_5143_ = lean_ctor_get(v___x_5142_, 1);
v_toEnvExtension_5144_ = lean_ctor_get(v_ext_5143_, 0);
v_asyncMode_5145_ = lean_ctor_get(v_toEnvExtension_5144_, 2);
v___x_5146_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5139_, v___x_5142_, v_env_5141_, v_asyncMode_5145_);
v_categories_5147_ = lean_ctor_get(v___x_5146_, 2);
lean_inc_ref(v_categories_5147_);
lean_dec(v___x_5146_);
v___x_5148_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_5149_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_5147_, v___x_5148_);
lean_dec_ref(v_categories_5147_);
if (lean_obj_tag(v___x_5149_) == 1)
{
lean_object* v_val_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5181_; 
v_val_5150_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5152_ = v___x_5149_;
v_isShared_5153_ = v_isSharedCheck_5181_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_val_5150_);
lean_dec(v___x_5149_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5181_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___y_5155_; lean_object* v___x_5164_; lean_object* v_toEnvExtension_5165_; lean_object* v_exportEntriesFn_5166_; lean_object* v_asyncMode_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v_importedEntries_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v_exported_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; uint8_t v___x_5177_; 
v___x_5164_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_5165_ = lean_ctor_get(v___x_5164_, 0);
v_exportEntriesFn_5166_ = lean_ctor_get(v___x_5164_, 4);
v_asyncMode_5167_ = lean_ctor_get(v_toEnvExtension_5165_, 2);
v___x_5168_ = lean_box(0);
lean_inc_ref_n(v_env_5141_, 2);
v___x_5169_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5138_, v_toEnvExtension_5165_, v_env_5141_, v_asyncMode_5167_, v___x_5168_);
v_importedEntries_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc_ref(v_importedEntries_5170_);
lean_dec(v___x_5169_);
v___x_5171_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5137_, v___x_5164_, v_env_5141_, v_asyncMode_5167_, v___x_5168_);
lean_inc_ref(v_exportEntriesFn_5166_);
v___x_5172_ = lean_apply_2(v_exportEntriesFn_5166_, v_env_5141_, v___x_5171_);
v_exported_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_exported_5173_);
lean_dec_ref(v___x_5172_);
v___x_5174_ = lean_array_push(v_importedEntries_5170_, v_exported_5173_);
v___x_5175_ = lean_unsigned_to_nat(0u);
v___x_5176_ = lean_array_get_size(v___x_5174_);
v___x_5177_ = lean_nat_dec_lt(v___x_5175_, v___x_5176_);
if (v___x_5177_ == 0)
{
lean_dec_ref(v___x_5174_);
v___y_5155_ = v___x_5137_;
goto v___jp_5154_;
}
else
{
size_t v___x_5178_; size_t v___x_5179_; lean_object* v___x_5180_; 
v___x_5178_ = ((size_t)0ULL);
v___x_5179_ = lean_usize_of_nat(v___x_5176_);
v___x_5180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_5174_, v___x_5178_, v___x_5179_, v___x_5137_);
lean_dec_ref(v___x_5174_);
v___y_5155_ = v___x_5180_;
goto v___jp_5154_;
}
v___jp_5154_:
{
lean_object* v_tables_5156_; lean_object* v_leadingTable_5157_; lean_object* v_trailingTable_5158_; lean_object* v_firstTokens_5159_; lean_object* v_firstTokens_5160_; lean_object* v___x_5162_; 
v_tables_5156_ = lean_ctor_get(v_val_5150_, 2);
v_leadingTable_5157_ = lean_ctor_get(v_tables_5156_, 0);
v_trailingTable_5158_ = lean_ctor_get(v_tables_5156_, 2);
lean_inc(v_trailingTable_5158_);
lean_inc(v_leadingTable_5157_);
lean_inc(v_val_5150_);
v_firstTokens_5159_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_5150_, v_leadingTable_5157_, v___y_5155_);
v_firstTokens_5160_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_5150_, v_trailingTable_5158_, v_firstTokens_5159_);
if (v_isShared_5153_ == 0)
{
lean_ctor_set_tag(v___x_5152_, 0);
lean_ctor_set(v___x_5152_, 0, v_firstTokens_5160_);
v___x_5162_ = v___x_5152_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_firstTokens_5160_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
else
{
lean_object* v___x_5182_; 
lean_dec(v___x_5149_);
lean_dec_ref(v_env_5141_);
v___x_5182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5137_);
return v___x_5182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
lean_object* v_res_5185_; 
v_res_5185_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_5183_);
lean_dec(v___y_5183_);
return v_res_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_){
_start:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v_env_5198_; lean_object* v___x_5199_; lean_object* v_toEnvExtension_5200_; lean_object* v_exportEntriesFn_5201_; lean_object* v_asyncMode_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v_importedEntries_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v_exported_5208_; lean_object* v___x_5209_; size_t v_sz_5210_; size_t v___x_5211_; lean_object* v___x_5212_; 
v___x_5194_ = lean_box(1);
v___x_5195_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_5196_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_5197_ = lean_st_ref_get(v_a_5192_);
v_env_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc_ref_n(v_env_5198_, 4);
lean_dec(v___x_5197_);
v___x_5199_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_5200_ = lean_ctor_get(v___x_5199_, 0);
v_exportEntriesFn_5201_ = lean_ctor_get(v___x_5199_, 4);
v_asyncMode_5202_ = lean_ctor_get(v_toEnvExtension_5200_, 2);
v___x_5203_ = lean_box(0);
v___x_5204_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5195_, v_toEnvExtension_5200_, v_env_5198_, v_asyncMode_5202_, v___x_5203_);
v_importedEntries_5205_ = lean_ctor_get(v___x_5204_, 0);
lean_inc_ref(v_importedEntries_5205_);
lean_dec(v___x_5204_);
v___x_5206_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_5194_, v___x_5199_, v_env_5198_, v_asyncMode_5202_, v___x_5203_);
lean_inc_ref(v_exportEntriesFn_5201_);
v___x_5207_ = lean_apply_2(v_exportEntriesFn_5201_, v_env_5198_, v___x_5206_);
v_exported_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_exported_5208_);
lean_dec_ref(v___x_5207_);
v___x_5209_ = lean_array_push(v_importedEntries_5205_, v_exported_5208_);
v_sz_5210_ = lean_array_size(v___x_5209_);
v___x_5211_ = ((size_t)0ULL);
v___x_5212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_5209_, v_sz_5210_, v___x_5211_, v___x_5194_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_);
lean_dec_ref(v___x_5209_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5236_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5215_ = v___x_5212_;
v_isShared_5216_ = v_isSharedCheck_5236_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5212_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5236_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5217_; lean_object* v_ext_5218_; lean_object* v_toEnvExtension_5219_; lean_object* v_asyncMode_5220_; lean_object* v___x_5221_; lean_object* v_categories_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5217_ = l_Lean_Parser_parserExtension;
v_ext_5218_ = lean_ctor_get(v___x_5217_, 1);
v_toEnvExtension_5219_ = lean_ctor_get(v_ext_5218_, 0);
v_asyncMode_5220_ = lean_ctor_get(v_toEnvExtension_5219_, 2);
lean_inc_ref(v_env_5198_);
v___x_5221_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5196_, v___x_5217_, v_env_5198_, v_asyncMode_5220_);
v_categories_5222_ = lean_ctor_get(v___x_5221_, 2);
lean_inc_ref(v_categories_5222_);
lean_dec(v___x_5221_);
v___x_5223_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_5224_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_5225_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_5222_, v___x_5224_);
lean_dec_ref(v_categories_5222_);
if (lean_obj_tag(v___x_5225_) == 1)
{
lean_object* v_val_5226_; lean_object* v___x_5227_; lean_object* v_a_5228_; lean_object* v_kinds_5229_; lean_object* v___x_5230_; lean_object* v___f_5231_; lean_object* v___x_5232_; 
lean_del_object(v___x_5215_);
v_val_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_val_5226_);
lean_dec_ref_known(v___x_5225_, 1);
v___x_5227_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_5192_);
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref(v___x_5227_);
v_kinds_5229_ = lean_ctor_get(v_val_5226_, 1);
lean_inc_ref(v_kinds_5229_);
lean_dec(v_val_5226_);
v___x_5230_ = lean_box(v_includeUnnamed_5188_);
v___f_5231_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5231_, 0, v_env_5198_);
lean_closure_set(v___f_5231_, 1, v___x_5203_);
lean_closure_set(v___f_5231_, 2, v_a_5213_);
lean_closure_set(v___f_5231_, 3, v_a_5228_);
lean_closure_set(v___f_5231_, 4, v___x_5230_);
v___x_5232_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_5229_, v___x_5223_, v___f_5231_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_);
lean_dec_ref(v_kinds_5229_);
return v___x_5232_;
}
else
{
lean_object* v___x_5234_; 
lean_dec(v___x_5225_);
lean_dec(v_a_5213_);
lean_dec_ref(v_env_5198_);
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 0, v___x_5223_);
v___x_5234_ = v___x_5215_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v___x_5223_);
v___x_5234_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
return v___x_5234_;
}
}
}
}
else
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
lean_dec_ref(v_env_5198_);
v_a_5237_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_5212_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5212_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5242_; 
if (v_isShared_5240_ == 0)
{
v___x_5242_ = v___x_5239_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_){
_start:
{
uint8_t v_includeUnnamed_boxed_5251_; lean_object* v_res_5252_; 
v_includeUnnamed_boxed_5251_ = lean_unbox(v_includeUnnamed_5245_);
v_res_5252_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_5251_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_);
lean_dec(v_a_5249_);
lean_dec_ref(v_a_5248_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_5253_, size_t v_sz_5254_, size_t v_i_5255_, lean_object* v_b_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v___x_5262_; 
v___x_5262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_5253_, v_sz_5254_, v_i_5255_, v_b_5256_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_5263_, lean_object* v_sz_5264_, lean_object* v_i_5265_, lean_object* v_b_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
size_t v_sz_boxed_5272_; size_t v_i_boxed_5273_; lean_object* v_res_5274_; 
v_sz_boxed_5272_ = lean_unbox_usize(v_sz_5264_);
lean_dec(v_sz_5264_);
v_i_boxed_5273_ = lean_unbox_usize(v_i_5265_);
lean_dec(v_i_5265_);
v_res_5274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_5263_, v_sz_boxed_5272_, v_i_boxed_5273_, v_b_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec_ref(v_as_5263_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v___x_5280_; 
v___x_5280_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_5278_);
return v___x_5280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
lean_object* v_res_5286_; 
v_res_5286_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_5287_, lean_object* v_00_u03b2_5288_, lean_object* v_map_5289_, lean_object* v_init_5290_, lean_object* v_f_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v___x_5297_; 
v___x_5297_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_5289_, v_init_5290_, v_f_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_);
return v___x_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_5298_, lean_object* v_00_u03b2_5299_, lean_object* v_map_5300_, lean_object* v_init_5301_, lean_object* v_f_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_){
_start:
{
lean_object* v_res_5308_; 
v_res_5308_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_5298_, v_00_u03b2_5299_, v_map_5300_, v_init_5301_, v_f_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec_ref(v_map_5300_);
return v_res_5308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_5309_, lean_object* v_f_5310_, lean_object* v_init_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
lean_object* v___x_5317_; 
v___x_5317_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5310_, v_map_5309_, v_init_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_);
return v___x_5317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_5318_, lean_object* v_f_5319_, lean_object* v_init_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v_res_5326_; 
v_res_5326_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_5318_, v_f_5319_, v_init_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_5327_, lean_object* v_00_u03c3_5328_, lean_object* v_00_u03b2_5329_, lean_object* v_map_5330_, lean_object* v_f_5331_, lean_object* v_init_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v___x_5338_; 
v___x_5338_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5331_, v_map_5330_, v_init_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_5339_, lean_object* v_00_u03c3_5340_, lean_object* v_00_u03b2_5341_, lean_object* v_map_5342_, lean_object* v_f_5343_, lean_object* v_init_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_5339_, v_00_u03c3_5340_, v_00_u03b2_5341_, v_map_5342_, v_f_5343_, v_init_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_5351_, lean_object* v_00_u03c3_5352_, lean_object* v_00_u03b1_5353_, lean_object* v_00_u03b2_5354_, lean_object* v_f_5355_, lean_object* v_x_5356_, lean_object* v_x_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_){
_start:
{
lean_object* v___x_5363_; 
v___x_5363_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_5355_, v_x_5356_, v_x_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_);
return v___x_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_5364_, lean_object* v_00_u03c3_5365_, lean_object* v_00_u03b1_5366_, lean_object* v_00_u03b2_5367_, lean_object* v_f_5368_, lean_object* v_x_5369_, lean_object* v_x_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_5364_, v_00_u03c3_5365_, v_00_u03b1_5366_, v_00_u03b2_5367_, v_f_5368_, v_x_5369_, v_x_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_5377_, lean_object* v_00_u03b2_5378_, lean_object* v_00_u03c3_5379_, lean_object* v_00_u03c3_5380_, lean_object* v_f_5381_, lean_object* v_as_5382_, size_t v_i_5383_, size_t v_stop_5384_, lean_object* v_b_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v___x_5391_; 
v___x_5391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_5381_, v_as_5382_, v_i_5383_, v_stop_5384_, v_b_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5392_, lean_object* v_00_u03b2_5393_, lean_object* v_00_u03c3_5394_, lean_object* v_00_u03c3_5395_, lean_object* v_f_5396_, lean_object* v_as_5397_, lean_object* v_i_5398_, lean_object* v_stop_5399_, lean_object* v_b_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
size_t v_i_boxed_5406_; size_t v_stop_boxed_5407_; lean_object* v_res_5408_; 
v_i_boxed_5406_ = lean_unbox_usize(v_i_5398_);
lean_dec(v_i_5398_);
v_stop_boxed_5407_ = lean_unbox_usize(v_stop_5399_);
lean_dec(v_stop_5399_);
v_res_5408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_5392_, v_00_u03b2_5393_, v_00_u03c3_5394_, v_00_u03c3_5395_, v_f_5396_, v_as_5397_, v_i_boxed_5406_, v_stop_boxed_5407_, v_b_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec(v___y_5402_);
lean_dec_ref(v___y_5401_);
lean_dec_ref(v_as_5397_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_5409_, lean_object* v_00_u03c3_5410_, lean_object* v_00_u03b1_5411_, lean_object* v_00_u03b2_5412_, lean_object* v_f_5413_, lean_object* v_keys_5414_, lean_object* v_vals_5415_, lean_object* v_heq_5416_, lean_object* v_i_5417_, lean_object* v_acc_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v___x_5424_; 
v___x_5424_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_5413_, v_keys_5414_, v_vals_5415_, v_i_5417_, v_acc_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_5425_, lean_object* v_00_u03c3_5426_, lean_object* v_00_u03b1_5427_, lean_object* v_00_u03b2_5428_, lean_object* v_f_5429_, lean_object* v_keys_5430_, lean_object* v_vals_5431_, lean_object* v_heq_5432_, lean_object* v_i_5433_, lean_object* v_acc_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_5425_, v_00_u03c3_5426_, v_00_u03b1_5427_, v_00_u03b2_5428_, v_f_5429_, v_keys_5430_, v_vals_5431_, v_heq_5432_, v_i_5433_, v_acc_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec_ref(v_vals_5431_);
lean_dec_ref(v_keys_5430_);
return v_res_5440_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_DocString_Add(uint8_t builtin);
lean_object* initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Doc(builtin);
}
#ifdef __cplusplus
}
#endif

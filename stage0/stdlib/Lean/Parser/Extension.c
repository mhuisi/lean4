// Lean compiler output
// Module: Lean.Parser.Extension
// Imports: public import Lean.Parser.Basic public import Lean.ScopedEnvExtension import Lean.BuiltinDocAttr
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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_List_eraseDupsBy___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_unsafeBaseIO___redArg(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_prattParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_initializing();
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Parser_categoryParserFnRef;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
extern lean_object* l_Lean_Parser_SyntaxStack_empty;
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinTokenTable;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinSyntaxNodeKindSetRef;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinParserCategoriesRef;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "parser category `"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` has already been defined"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0 = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0_value)}};
static const lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1 = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0_value)}};
static const lean_object* l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0 = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_ParserExtension_instInhabitedEntry_default = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_ParserExtension_instInhabitedEntry = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object*);
static lean_once_cell_t l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_instInhabitedState;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid empty symbol"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__0_value)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unknown parser category `"};
static const lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0_value;
static const lean_string_object l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_getCategory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_getCategory___closed__0 = (const lean_object*)&l_Lean_Parser_getCategory___closed__0_value;
static const lean_closure_object l_Lean_Parser_getCategory___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_getCategory___closed__1 = (const lean_object*)&l_Lean_Parser_getCategory___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object*, lean_object*);
static const lean_closure_object l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0 = (const lean_object*)&l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid builtin parser `"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`, "};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object*);
static const lean_string_object l_Lean_Parser_ParserExtension_addEntryImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Parser.Extension"};
static const lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__0 = (const lean_object*)&l_Lean_Parser_ParserExtension_addEntryImpl___closed__0_value;
static const lean_string_object l_Lean_Parser_ParserExtension_addEntryImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Parser.ParserExtension.addEntryImpl"};
static const lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__1 = (const lean_object*)&l_Lean_Parser_ParserExtension_addEntryImpl___closed__1_value;
static const lean_string_object l_Lean_Parser_ParserExtension_addEntryImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ParserExtension.addEntryImpl: "};
static const lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__2 = (const lean_object*)&l_Lean_Parser_ParserExtension_addEntryImpl___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_registerAliasCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "aliases can only be registered during initialization"};
static const lean_object* l_Lean_Parser_registerAliasCore___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_registerAliasCore___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Parser_registerAliasCore___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerAliasCore___redArg___closed__1;
static const lean_string_object l_Lean_Parser_registerAliasCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "alias `"};
static const lean_object* l_Lean_Parser_registerAliasCore___redArg___closed__2 = (const lean_object*)&l_Lean_Parser_registerAliasCore___redArg___closed__2_value;
static const lean_string_object l_Lean_Parser_registerAliasCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_Parser_registerAliasCore___redArg___closed__3 = (const lean_object*)&l_Lean_Parser_registerAliasCore___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_getConstAlias___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parser `"};
static const lean_object* l_Lean_Parser_getConstAlias___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_getConstAlias___redArg___closed__0_value;
static const lean_string_object l_Lean_Parser_getConstAlias___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` was not found"};
static const lean_object* l_Lean_Parser_getConstAlias___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_getConstAlias___redArg___closed__1_value;
static const lean_string_object l_Lean_Parser_getConstAlias___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` is not a constant, it takes one argument"};
static const lean_object* l_Lean_Parser_getConstAlias___redArg___closed__2 = (const lean_object*)&l_Lean_Parser_getConstAlias___redArg___closed__2_value;
static const lean_string_object l_Lean_Parser_getConstAlias___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "` is not a constant, it takes two arguments"};
static const lean_object* l_Lean_Parser_getConstAlias___redArg___closed__3 = (const lean_object*)&l_Lean_Parser_getConstAlias___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_getUnaryAlias___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` does not take one argument"};
static const lean_object* l_Lean_Parser_getUnaryAlias___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_getUnaryAlias___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_getBinaryAlias___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` does not take two arguments"};
static const lean_object* l_Lean_Parser_getBinaryAlias___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_getBinaryAlias___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAliasesRef;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAlias2kindRef;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAliases2infoRef;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_getParserAliasInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_getParserAliasInfo___closed__0 = (const lean_object*)&l_Lean_Parser_getParserAliasInfo___closed__0_value;
static const lean_ctor_object l_Lean_Parser_getParserAliasInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_getParserAliasInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_getParserAliasInfo___closed__1 = (const lean_object*)&l_Lean_Parser_getParserAliasInfo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_instCoeParserParserAliasValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instCoeParserParserAliasValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instCoeParserParserAliasValue___closed__0 = (const lean_object*)&l_Lean_Parser_instCoeParserParserAliasValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instCoeParserParserAliasValue = (const lean_object*)&l_Lean_Parser_instCoeParserParserAliasValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_instCoeForallParserParserAliasValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___closed__0 = (const lean_object*)&l_Lean_Parser_instCoeForallParserParserAliasValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue = (const lean_object*)&l_Lean_Parser_instCoeForallParserParserAliasValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_instCoeForallParserForallParserAliasValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___closed__0 = (const lean_object*)&l_Lean_Parser_instCoeForallParserForallParserAliasValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue = (const lean_object*)&l_Lean_Parser_instCoeForallParserForallParserAliasValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unexpected parser type at `"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__0 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__0_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "` (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected)"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__1 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__1_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__2 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__2_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__3 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__4 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "TrailingParser"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__5 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__5_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ParserDescr"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__6 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__6_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "TrailingParserDescr"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__7 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAttributeHooks;
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 58, 155, 4, 51, 160, 88)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 52, 234, 177, 21, 192, 22, 198)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(76, 45, 242, 72, 67, 202, 5, 30)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(205, 229, 28, 218, 19, 105, 170, 35)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 61, 201, 18, 105, 219, 240, 138)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 138, 216, 176, 146, 185, 210, 47)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 125, 145, 169, 32, 215, 69, 54)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(105, 155, 228, 215, 194, 242, 73, 58)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(244, 229, 229, 196, 152, 62, 92, 225)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(154, 168, 69, 111, 155, 198, 82, 16)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "run_builtin_parser_attribute_hooks"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 253, 249, 46, 168, 175, 6, 195)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "explicitly run hooks normally activated by builtin parser attributes"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "run_parser_attribute_hooks"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 66, 27, 152, 146, 188, 80, 181)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "explicitly run hooks normally activated by parser attributes"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "parserExtension"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 242, 71, 245, 68, 132, 173, 111)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ParserExtension_Entry_toOLeanEntry, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ParserExtension_addEntryImpl, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "internal"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "parseQuotWithCurrentStage"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(177, 49, 45, 44, 152, 148, 209, 41)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 253, 75, 217, 201, 67, 21, 43)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "(Lean bootstrapping) use parsers from the current stage inside quotations"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(197, 200, 93, 246, 219, 188, 139, 219)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 175, 65, 251, 248, 238, 117, 156)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_internal_parseQuotWithCurrentStage;
static const lean_string_object l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_evalInsideQuot___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "interpreter"};
static const lean_object* l_Lean_Parser_evalInsideQuot___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__0_value;
static const lean_string_object l_Lean_Parser_evalInsideQuot___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "prefer_native"};
static const lean_object* l_Lean_Parser_evalInsideQuot___lam__0___closed__1 = (const lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Parser_evalInsideQuot___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 89, 165, 10, 241, 76, 182, 215)}};
static const lean_ctor_object l_Lean_Parser_evalInsideQuot___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 111, 178, 130, 77, 52, 174, 36)}};
static const lean_object* l_Lean_Parser_evalInsideQuot___lam__0___closed__2 = (const lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_evalInsideQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_evalInsideQuot___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_evalInsideQuot___closed__0 = (const lean_object*)&l_Lean_Parser_evalInsideQuot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_categoryParserFnImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__0 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__0_value;
static const lean_ctor_object l_Lean_Parser_categoryParserFnImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 107, 139, 89, 122, 253, 8, 100)}};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__1 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__1_value;
static const lean_string_object l_Lean_Parser_categoryParserFnImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unknown parser category '"};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__2 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__2_value;
static const lean_string_object l_Lean_Parser_categoryParserFnImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__3 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__3_value;
static const lean_string_object l_Lean_Parser_categoryParserFnImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "stx"};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__4 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__4_value;
static const lean_ctor_object l_Lean_Parser_categoryParserFnImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(89, 124, 230, 186, 154, 11, 21, 78)}};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__5 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_categoryParserFnImpl, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Parser_isValidSyntaxNodeKind___closed__0;
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_getSyntaxNodeKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_getSyntaxNodeKinds___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_getSyntaxNodeKinds___closed__0 = (const lean_object*)&l_Lean_Parser_getSyntaxNodeKinds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object*);
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__0 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__1 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__1_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__2 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__2_value;
static const lean_array_object l_Lean_Parser_mkInputContext___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__3 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__3_value;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__4 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__4_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__5 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__5_value;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__6 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__7 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__7_value;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__8 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__9 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__9_value;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__10;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__11;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__12 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__12_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_2),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__13 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__13_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__7_value),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__3_value)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__14 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__14_value;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__15;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__16;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__17;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__18;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__19;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__20;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__21;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__22;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__23;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__24;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__25;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__26;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__27;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_mkParserState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_mkParserState___closed__0 = (const lean_object*)&l_Lean_Parser_mkParserState___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_runParserCategory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_whitespace, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_runParserCategory___closed__0 = (const lean_object*)&l_Lean_Parser_runParserCategory___closed__0_value;
static const lean_string_object l_Lean_Parser_runParserCategory___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of input"};
static const lean_object* l_Lean_Parser_runParserCategory___closed__1 = (const lean_object*)&l_Lean_Parser_runParserCategory___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_declareLeadingBuiltinParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "addBuiltinLeadingParser"};
static const lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__0 = (const lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__0_value;
static const lean_ctor_object l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 143, 237, 9, 185, 72, 31, 190)}};
static const lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1 = (const lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_declareTrailingBuiltinParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "addBuiltinTrailingParser"};
static const lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__0 = (const lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__0_value;
static const lean_ctor_object l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 81, 8, 5, 195, 158, 30, 32)}};
static const lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__1 = (const lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_getParserPriority___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Invalid parser attribute: No argument or numeral expected"};
static const lean_object* l_Lean_Parser_getParserPriority___closed__0 = (const lean_object*)&l_Lean_Parser_getParserPriority___closed__0_value;
static const lean_ctor_object l_Lean_Parser_getParserPriority___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_getParserPriority___closed__0_value)}};
static const lean_object* l_Lean_Parser_getParserPriority___closed__1 = (const lean_object*)&l_Lean_Parser_getParserPriority___closed__1_value;
static const lean_string_object l_Lean_Parser_getParserPriority___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Invalid parser attribute: Numeral expected, but found `"};
static const lean_object* l_Lean_Parser_getParserPriority___closed__2 = (const lean_object*)&l_Lean_Parser_getParserPriority___closed__2_value;
static const lean_ctor_object l_Lean_Parser_getParserPriority___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_getParserPriority___closed__3 = (const lean_object*)&l_Lean_Parser_getParserPriority___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "Unexpected type for parser declaration: Parsers must have type `Parser` or `TrailingParser`, but `"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0_value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2_value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__4 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__4_value;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__5 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__5_value;
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7_value;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`declName` should be in Lean.Parser.Category"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__0 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__0_value;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Category"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__2 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__2_value;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Builtin parser"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__3 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invalid parser `"};
static const lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0 = (const lean_object*)&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0_value;
static lean_once_cell_t l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1;
static lean_once_cell_t l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkParserAttributeImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parser"};
static const lean_object* l_Lean_Parser_mkParserAttributeImpl___closed__0 = (const lean_object*)&l_Lean_Parser_mkParserAttributeImpl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "invalid parser attribute implementation builder arguments"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "parserAttr"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 245, 154, 169, 111, 55, 1, 167)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtin_term_parser"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 207, 87, 145, 239, 20, 239, 169)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__2_value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(208, 211, 65, 28, 248, 161, 130, 58)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)(((size_t)(346849000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(211, 245, 159, 105, 210, 84, 228, 140)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 27, 163, 230, 210, 150, 171, 72)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 94, 18, 83, 183, 97, 76, 247)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(53, 114, 123, 211, 41, 25, 101, 118)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term_parser"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 63, 227, 232, 74, 240, 13, 112)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "builtin_command_parser"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 82, 248, 24, 98, 200, 69, 241)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__2_value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 37, 169, 7, 189, 210, 168, 21)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "command_parser"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 48, 168, 200, 51, 243, 130, 78)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withOpenDeclFnCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__0 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value;
static const lean_string_object l_Lean_Parser_withOpenDeclFnCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__1 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__1_value;
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__2 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__2_value;
static const lean_string_object l_Lean_Parser_withOpenDeclFnCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__3 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__3_value;
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(55, 166, 237, 23, 37, 47, 5, 133)}};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__4 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withOpenFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l_Lean_Parser_withOpenFn___closed__0 = (const lean_object*)&l_Lean_Parser_withOpenFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withOpenFn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withOpenFn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenFn___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withOpenFn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenFn___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_withOpenFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenFn___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_withOpenFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 8, 226, 43, 107, 167, 95, 157)}};
static const lean_object* l_Lean_Parser_withOpenFn___closed__1 = (const lean_object*)&l_Lean_Parser_withOpenFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withSetOptionFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l_Lean_Parser_withSetOptionFn___closed__0 = (const lean_object*)&l_Lean_Parser_withSetOptionFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withSetOptionFn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withSetOptionFn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withSetOptionFn___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withSetOptionFn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withSetOptionFn___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_withSetOptionFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withSetOptionFn___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_withSetOptionFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 223, 149, 245, 150, 86, 134, 198)}};
static const lean_object* l_Lean_Parser_withSetOptionFn___closed__1 = (const lean_object*)&l_Lean_Parser_withSetOptionFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_aliasExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ambiguous parser name "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__0 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__0_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "unknown parser "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__1 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__1_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "expected parser to return exactly one syntax object"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__2 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__2_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parser alias "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__3 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__3_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = ", must not take parameters"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__4 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__4_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 103, .m_capacity = 103, .m_length = 102, .m_data = "failed to determine parser using syntax stack, the specified element on the stack is not an identifier"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__5 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__5_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "failed to determine parser using syntax stack, stack is too small"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__6 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_parserOfStack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_parserOfStack___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_parserOfStack___closed__0 = (const lean_object*)&l_Lean_Parser_parserOfStack___closed__0_value;
static const lean_closure_object l_Lean_Parser_parserOfStack___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_parserOfStack___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_parserOfStack___closed__1 = (const lean_object*)&l_Lean_Parser_parserOfStack___closed__1_value;
static const lean_ctor_object l_Lean_Parser_parserOfStack___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_parserOfStack___closed__0_value),((lean_object*)&l_Lean_Parser_parserOfStack___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_parserOfStack___closed__2 = (const lean_object*)&l_Lean_Parser_parserOfStack___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_4_ = lean_st_mk_ref(v___x_3_);
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2____boxed(lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
return v_res_7_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_8_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_13_ = lean_st_mk_ref(v___x_12_);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2____boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object* v_k_17_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_19_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_20_ = lean_st_ref_take(v___x_19_);
v___x_21_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v___x_20_, v_k_17_);
v___x_22_ = lean_st_ref_put(v___x_19_, v___x_21_);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind___boxed(lean_object* v_k_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Parser_registerBuiltinNodeKind(v_k_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_59_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_58_);
lean_dec_ref(v___x_59_);
v___x_60_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_61_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_60_);
lean_dec_ref(v___x_61_);
v___x_62_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_63_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_62_);
lean_dec_ref(v___x_63_);
v___x_64_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_65_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_64_);
lean_dec_ref(v___x_65_);
v___x_66_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_67_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_66_);
lean_dec_ref(v___x_67_);
v___x_68_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_69_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_68_);
lean_dec_ref(v___x_69_);
v___x_70_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_71_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_70_);
lean_dec_ref(v___x_71_);
v___x_72_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_73_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_72_);
lean_dec_ref(v___x_73_);
v___x_74_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_75_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_74_);
lean_dec_ref(v___x_75_);
v___x_76_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_77_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2____boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_();
return v_res_79_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_80_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_85_ = lean_st_mk_ref(v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(lean_object* v_catName_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0));
v___x_93_ = 1;
v___x_94_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_91_, v___x_93_);
v___x_95_ = lean_string_append(v___x_92_, v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1));
v___x_97_ = lean_string_append(v___x_95_, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object* v_00_u03b1_99_, lean_object* v_catName_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_102_, lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
lean_object* v_ks_106_; lean_object* v_vs_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_131_; 
v_ks_106_ = lean_ctor_get(v_x_102_, 0);
v_vs_107_ = lean_ctor_get(v_x_102_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_131_ == 0)
{
v___x_109_ = v_x_102_;
v_isShared_110_ = v_isSharedCheck_131_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_vs_107_);
lean_inc(v_ks_106_);
lean_dec(v_x_102_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_131_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_array_get_size(v_ks_106_);
v___x_112_ = lean_nat_dec_lt(v_x_103_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
lean_dec(v_x_103_);
v___x_113_ = lean_array_push(v_ks_106_, v_x_104_);
v___x_114_ = lean_array_push(v_vs_107_, v_x_105_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_114_);
lean_ctor_set(v___x_109_, 0, v___x_113_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v_k_x27_118_; uint8_t v___x_119_; 
v_k_x27_118_ = lean_array_fget_borrowed(v_ks_106_, v_x_103_);
v___x_119_ = lean_name_eq(v_x_104_, v_k_x27_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_121_; 
if (v_isShared_110_ == 0)
{
v___x_121_ = v___x_109_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_ks_106_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_vs_107_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_add(v_x_103_, v___x_122_);
lean_dec(v_x_103_);
v_x_102_ = v___x_121_;
v_x_103_ = v___x_123_;
goto _start;
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_126_ = lean_array_fset(v_ks_106_, v_x_103_, v_x_104_);
v___x_127_ = lean_array_fset(v_vs_107_, v_x_103_, v_x_105_);
lean_dec(v_x_103_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_127_);
lean_ctor_set(v___x_109_, 0, v___x_126_);
v___x_129_ = v___x_109_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(lean_object* v_n_132_, lean_object* v_k_133_, lean_object* v_v_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_n_132_, v___x_135_, v_k_133_, v_v_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object* v_x_138_, size_t v_x_139_, size_t v_x_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_es_143_; size_t v___x_144_; size_t v___x_145_; lean_object* v_j_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_es_143_ = lean_ctor_get(v_x_138_, 0);
v___x_144_ = ((size_t)31ULL);
v___x_145_ = lean_usize_land(v_x_139_, v___x_144_);
v_j_146_ = lean_usize_to_nat(v___x_145_);
v___x_147_ = lean_array_get_size(v_es_143_);
v___x_148_ = lean_nat_dec_lt(v_j_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec(v_j_146_);
lean_dec(v_x_142_);
lean_dec(v_x_141_);
return v_x_138_;
}
else
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_187_; 
lean_inc_ref(v_es_143_);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_x_138_, 0);
lean_dec(v_unused_188_);
v___x_150_ = v_x_138_;
v_isShared_151_ = v_isSharedCheck_187_;
goto v_resetjp_149_;
}
else
{
lean_dec(v_x_138_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_187_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v_v_152_; lean_object* v___x_153_; lean_object* v_xs_x27_154_; lean_object* v___y_156_; 
v_v_152_ = lean_array_fget(v_es_143_, v_j_146_);
v___x_153_ = lean_box(0);
v_xs_x27_154_ = lean_array_fset(v_es_143_, v_j_146_, v___x_153_);
switch(lean_obj_tag(v_v_152_))
{
case 0:
{
lean_object* v_key_161_; lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_172_; 
v_key_161_ = lean_ctor_get(v_v_152_, 0);
v_val_162_ = lean_ctor_get(v_v_152_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_v_152_);
if (v_isSharedCheck_172_ == 0)
{
v___x_164_ = v_v_152_;
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_inc(v_key_161_);
lean_dec(v_v_152_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
uint8_t v___x_166_; 
v___x_166_ = lean_name_eq(v_x_141_, v_key_161_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_del_object(v___x_164_);
v___x_167_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_161_, v_val_162_, v_x_141_, v_x_142_);
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
v___y_156_ = v___x_168_;
goto v___jp_155_;
}
else
{
lean_object* v___x_170_; 
lean_dec(v_val_162_);
lean_dec(v_key_161_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_x_142_);
lean_ctor_set(v___x_164_, 0, v_x_141_);
v___x_170_ = v___x_164_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_x_141_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_x_142_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
v___y_156_ = v___x_170_;
goto v___jp_155_;
}
}
}
}
case 1:
{
lean_object* v_node_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_node_173_ = lean_ctor_get(v_v_152_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_v_152_);
if (v_isSharedCheck_185_ == 0)
{
v___x_175_ = v_v_152_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_node_173_);
lean_dec(v_v_152_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_usize_shift_right(v_x_139_, v___x_177_);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_add(v_x_140_, v___x_179_);
v___x_181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_node_173_, v___x_178_, v___x_180_, v_x_141_, v_x_142_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_181_);
v___x_183_ = v___x_175_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
v___y_156_ = v___x_183_;
goto v___jp_155_;
}
}
}
default: 
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_x_141_);
lean_ctor_set(v___x_186_, 1, v_x_142_);
v___y_156_ = v___x_186_;
goto v___jp_155_;
}
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = lean_array_fset(v_xs_x27_154_, v_j_146_, v___y_156_);
lean_dec(v_j_146_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_157_);
v___x_159_ = v___x_150_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
else
{
lean_object* v_ks_189_; lean_object* v_vs_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_210_; 
v_ks_189_ = lean_ctor_get(v_x_138_, 0);
v_vs_190_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_210_ == 0)
{
v___x_192_ = v_x_138_;
v_isShared_193_ = v_isSharedCheck_210_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_vs_190_);
lean_inc(v_ks_189_);
lean_dec(v_x_138_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_210_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_ks_189_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_vs_190_);
v___x_195_ = v_reuseFailAlloc_209_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v_newNode_196_; uint8_t v___y_198_; size_t v___x_204_; uint8_t v___x_205_; 
v_newNode_196_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v___x_195_, v_x_141_, v_x_142_);
v___x_204_ = ((size_t)7ULL);
v___x_205_ = lean_usize_dec_le(v___x_204_, v_x_140_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_196_);
v___x_207_ = lean_unsigned_to_nat(4u);
v___x_208_ = lean_nat_dec_lt(v___x_206_, v___x_207_);
lean_dec(v___x_206_);
v___y_198_ = v___x_208_;
goto v___jp_197_;
}
else
{
v___y_198_ = v___x_205_;
goto v___jp_197_;
}
v___jp_197_:
{
if (v___y_198_ == 0)
{
lean_object* v_ks_199_; lean_object* v_vs_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_ks_199_ = lean_ctor_get(v_newNode_196_, 0);
lean_inc_ref(v_ks_199_);
v_vs_200_ = lean_ctor_get(v_newNode_196_, 1);
lean_inc_ref(v_vs_200_);
lean_dec_ref(v_newNode_196_);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0);
v___x_203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_x_140_, v_ks_199_, v_vs_200_, v___x_201_, v___x_202_);
lean_dec_ref(v_vs_200_);
lean_dec_ref(v_ks_199_);
return v___x_203_;
}
else
{
return v_newNode_196_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_211_, lean_object* v_keys_212_, lean_object* v_vals_213_, lean_object* v_i_214_, lean_object* v_entries_215_){
_start:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_array_get_size(v_keys_212_);
v___x_217_ = lean_nat_dec_lt(v_i_214_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_i_214_);
return v_entries_215_;
}
else
{
lean_object* v_k_218_; lean_object* v_v_219_; uint64_t v___y_221_; 
v_k_218_ = lean_array_fget_borrowed(v_keys_212_, v_i_214_);
v_v_219_ = lean_array_fget_borrowed(v_vals_213_, v_i_214_);
if (lean_obj_tag(v_k_218_) == 0)
{
uint64_t v___x_232_; 
v___x_232_ = 1723ULL;
v___y_221_ = v___x_232_;
goto v___jp_220_;
}
else
{
uint64_t v_hash_233_; 
v_hash_233_ = lean_ctor_get_uint64(v_k_218_, sizeof(void*)*2);
v___y_221_ = v_hash_233_;
goto v___jp_220_;
}
v___jp_220_:
{
size_t v_h_222_; size_t v___x_223_; lean_object* v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v_h_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_h_222_ = lean_uint64_to_usize(v___y_221_);
v___x_223_ = ((size_t)5ULL);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_sub(v_depth_211_, v___x_225_);
v___x_227_ = lean_usize_mul(v___x_223_, v___x_226_);
v_h_228_ = lean_usize_shift_right(v_h_222_, v___x_227_);
v___x_229_ = lean_nat_add(v_i_214_, v___x_224_);
lean_dec(v_i_214_);
lean_inc(v_v_219_);
lean_inc(v_k_218_);
v___x_230_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_entries_215_, v_h_228_, v_depth_211_, v_k_218_, v_v_219_);
v_i_214_ = v___x_229_;
v_entries_215_ = v___x_230_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_234_, lean_object* v_keys_235_, lean_object* v_vals_236_, lean_object* v_i_237_, lean_object* v_entries_238_){
_start:
{
size_t v_depth_boxed_239_; lean_object* v_res_240_; 
v_depth_boxed_239_ = lean_unbox_usize(v_depth_234_);
lean_dec(v_depth_234_);
v_res_240_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_239_, v_keys_235_, v_vals_236_, v_i_237_, v_entries_238_);
lean_dec_ref(v_vals_236_);
lean_dec_ref(v_keys_235_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
size_t v_x_533__boxed_246_; size_t v_x_534__boxed_247_; lean_object* v_res_248_; 
v_x_533__boxed_246_ = lean_unbox_usize(v_x_242_);
lean_dec(v_x_242_);
v_x_534__boxed_247_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_res_248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_241_, v_x_533__boxed_246_, v_x_534__boxed_247_, v_x_244_, v_x_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
uint64_t v___y_253_; 
if (lean_obj_tag(v_x_250_) == 0)
{
uint64_t v___x_257_; 
v___x_257_ = 1723ULL;
v___y_253_ = v___x_257_;
goto v___jp_252_;
}
else
{
uint64_t v_hash_258_; 
v_hash_258_ = lean_ctor_get_uint64(v_x_250_, sizeof(void*)*2);
v___y_253_ = v_hash_258_;
goto v___jp_252_;
}
v___jp_252_:
{
size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_uint64_to_usize(v___y_253_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_249_, v___x_254_, v___x_255_, v_x_250_, v_x_251_);
return v___x_256_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_259_, lean_object* v_i_260_, lean_object* v_k_261_){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_array_get_size(v_keys_259_);
v___x_263_ = lean_nat_dec_lt(v_i_260_, v___x_262_);
if (v___x_263_ == 0)
{
lean_dec(v_i_260_);
return v___x_263_;
}
else
{
lean_object* v_k_x27_264_; uint8_t v___x_265_; 
v_k_x27_264_ = lean_array_fget_borrowed(v_keys_259_, v_i_260_);
v___x_265_ = lean_name_eq(v_k_261_, v_k_x27_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_add(v_i_260_, v___x_266_);
lean_dec(v_i_260_);
v_i_260_ = v___x_267_;
goto _start;
}
else
{
lean_dec(v_i_260_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_269_, lean_object* v_i_270_, lean_object* v_k_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_269_, v_i_270_, v_k_271_);
lean_dec(v_k_271_);
lean_dec_ref(v_keys_269_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object* v_x_274_, size_t v_x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v_es_277_; lean_object* v___x_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v_j_281_; lean_object* v___x_282_; 
v_es_277_ = lean_ctor_get(v_x_274_, 0);
v___x_278_ = lean_box(2);
v___x_279_ = ((size_t)31ULL);
v___x_280_ = lean_usize_land(v_x_275_, v___x_279_);
v_j_281_ = lean_usize_to_nat(v___x_280_);
v___x_282_ = lean_array_get_borrowed(v___x_278_, v_es_277_, v_j_281_);
lean_dec(v_j_281_);
switch(lean_obj_tag(v___x_282_))
{
case 0:
{
lean_object* v_key_283_; uint8_t v___x_284_; 
v_key_283_ = lean_ctor_get(v___x_282_, 0);
v___x_284_ = lean_name_eq(v_x_276_, v_key_283_);
return v___x_284_;
}
case 1:
{
lean_object* v_node_285_; size_t v___x_286_; size_t v___x_287_; 
v_node_285_ = lean_ctor_get(v___x_282_, 0);
v___x_286_ = ((size_t)5ULL);
v___x_287_ = lean_usize_shift_right(v_x_275_, v___x_286_);
v_x_274_ = v_node_285_;
v_x_275_ = v___x_287_;
goto _start;
}
default: 
{
uint8_t v___x_289_; 
v___x_289_ = 0;
return v___x_289_;
}
}
}
else
{
lean_object* v_ks_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_ks_290_ = lean_ctor_get(v_x_274_, 0);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_ks_290_, v___x_291_, v_x_276_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
size_t v_x_721__boxed_296_; uint8_t v_res_297_; lean_object* v_r_298_; 
v_x_721__boxed_296_ = lean_unbox_usize(v_x_294_);
lean_dec(v_x_294_);
v_res_297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_293_, v_x_721__boxed_296_, v_x_295_);
lean_dec(v_x_295_);
lean_dec_ref(v_x_293_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
uint64_t v___y_302_; 
if (lean_obj_tag(v_x_300_) == 0)
{
uint64_t v___x_305_; 
v___x_305_ = 1723ULL;
v___y_302_ = v___x_305_;
goto v___jp_301_;
}
else
{
uint64_t v_hash_306_; 
v_hash_306_ = lean_ctor_get_uint64(v_x_300_, sizeof(void*)*2);
v___y_302_ = v_hash_306_;
goto v___jp_301_;
}
v___jp_301_:
{
size_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_uint64_to_usize(v___y_302_);
v___x_304_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_299_, v___x_303_, v_x_300_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_307_, v_x_308_);
lean_dec(v_x_308_);
lean_dec_ref(v_x_307_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* v_categories_311_, lean_object* v_catName_312_, lean_object* v_initial_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_311_, v_catName_312_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_311_, v_catName_312_, v_initial_313_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; 
lean_dec_ref(v_initial_313_);
lean_dec_ref(v_categories_311_);
v___x_317_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_312_);
return v___x_317_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object* v_00_u03b2_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_319_, v_x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object* v_00_u03b2_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
uint8_t v_res_325_; lean_object* v_r_326_; 
v_res_325_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(v_00_u03b2_322_, v_x_323_, v_x_324_);
lean_dec(v_x_324_);
lean_dec_ref(v_x_323_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object* v_00_u03b2_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_x_328_, v_x_329_, v_x_330_);
return v___x_331_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object* v_00_u03b2_332_, lean_object* v_x_333_, size_t v_x_334_, lean_object* v_x_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_333_, v_x_334_, v_x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
size_t v_x_802__boxed_341_; uint8_t v_res_342_; lean_object* v_r_343_; 
v_x_802__boxed_341_ = lean_unbox_usize(v_x_339_);
lean_dec(v_x_339_);
v_res_342_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(v_00_u03b2_337_, v_x_338_, v_x_802__boxed_341_, v_x_340_);
lean_dec(v_x_340_);
lean_dec_ref(v_x_338_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object* v_00_u03b2_344_, lean_object* v_x_345_, size_t v_x_346_, size_t v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_345_, v_x_346_, v_x_347_, v_x_348_, v_x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
size_t v_x_813__boxed_357_; size_t v_x_814__boxed_358_; lean_object* v_res_359_; 
v_x_813__boxed_357_ = lean_unbox_usize(v_x_353_);
lean_dec(v_x_353_);
v_x_814__boxed_358_ = lean_unbox_usize(v_x_354_);
lean_dec(v_x_354_);
v_res_359_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(v_00_u03b2_351_, v_x_352_, v_x_813__boxed_357_, v_x_814__boxed_358_, v_x_355_, v_x_356_);
return v_res_359_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_360_, lean_object* v_keys_361_, lean_object* v_vals_362_, lean_object* v_heq_363_, lean_object* v_i_364_, lean_object* v_k_365_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_361_, v_i_364_, v_k_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_367_, lean_object* v_keys_368_, lean_object* v_vals_369_, lean_object* v_heq_370_, lean_object* v_i_371_, lean_object* v_k_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(v_00_u03b2_367_, v_keys_368_, v_vals_369_, v_heq_370_, v_i_371_, v_k_372_);
lean_dec(v_k_372_);
lean_dec_ref(v_vals_369_);
lean_dec_ref(v_keys_368_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_375_, lean_object* v_n_376_, lean_object* v_k_377_, lean_object* v_v_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v_n_376_, v_k_377_, v_v_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_380_, size_t v_depth_381_, lean_object* v_keys_382_, lean_object* v_vals_383_, lean_object* v_heq_384_, lean_object* v_i_385_, lean_object* v_entries_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_381_, v_keys_382_, v_vals_383_, v_i_385_, v_entries_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_388_, lean_object* v_depth_389_, lean_object* v_keys_390_, lean_object* v_vals_391_, lean_object* v_heq_392_, lean_object* v_i_393_, lean_object* v_entries_394_){
_start:
{
size_t v_depth_boxed_395_; lean_object* v_res_396_; 
v_depth_boxed_395_ = lean_unbox_usize(v_depth_389_);
lean_dec(v_depth_389_);
v_res_396_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(v_00_u03b2_388_, v_depth_boxed_395_, v_keys_390_, v_vals_391_, v_heq_392_, v_i_393_, v_entries_394_);
lean_dec_ref(v_vals_391_);
lean_dec_ref(v_keys_390_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_398_, v_x_399_, v_x_400_, v_x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object* v_e_403_){
_start:
{
if (lean_obj_tag(v_e_403_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_a_405_ = lean_ctor_get(v_e_403_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_e_403_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v_e_403_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v_e_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_mk_io_user_error(v_a_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 1);
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_a_414_ = lean_ctor_get(v_e_403_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_e_403_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v_e_403_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v_e_403_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 0);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object* v_e_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object* v_00_u03b1_425_, lean_object* v_e_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object* v_00_u03b1_429_, lean_object* v_e_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(v_00_u03b1_429_, v_e_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* v_catName_436_, lean_object* v_declName_437_, uint8_t v_behavior_438_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_440_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_441_ = lean_st_ref_get(v___x_440_);
v___x_442_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_443_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_444_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_444_, 0, v_declName_437_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*3, v_behavior_438_);
v___x_445_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(v___x_441_, v_catName_436_, v___x_444_);
v___x_446_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_456_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_456_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_451_ = lean_st_ref_swap(v___x_440_, v_a_447_);
lean_dec(v___x_451_);
v___x_452_ = lean_box(0);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_446_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_446_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* v_catName_465_, lean_object* v_declName_466_, lean_object* v_behavior_467_, lean_object* v_a_468_){
_start:
{
uint8_t v_behavior_boxed_469_; lean_object* v_res_470_; 
v_behavior_boxed_469_ = lean_unbox(v_behavior_467_);
v_res_470_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_465_, v_declName_466_, v_behavior_boxed_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object* v_x_471_){
_start:
{
switch(lean_obj_tag(v_x_471_))
{
case 0:
{
lean_object* v___x_472_; 
v___x_472_ = lean_unsigned_to_nat(0u);
return v___x_472_;
}
case 1:
{
lean_object* v___x_473_; 
v___x_473_ = lean_unsigned_to_nat(1u);
return v___x_473_;
}
case 2:
{
lean_object* v___x_474_; 
v___x_474_ = lean_unsigned_to_nat(2u);
return v___x_474_;
}
default: 
{
lean_object* v___x_475_; 
v___x_475_ = lean_unsigned_to_nat(3u);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object* v_x_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(v_x_476_);
lean_dec_ref(v_x_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_478_, lean_object* v_k_479_){
_start:
{
switch(lean_obj_tag(v_t_478_))
{
case 0:
{
lean_object* v_val_480_; lean_object* v___x_481_; 
v_val_480_ = lean_ctor_get(v_t_478_, 0);
lean_inc_ref(v_val_480_);
lean_dec_ref_known(v_t_478_, 1);
v___x_481_ = lean_apply_1(v_k_479_, v_val_480_);
return v___x_481_;
}
case 1:
{
lean_object* v_val_482_; lean_object* v___x_483_; 
v_val_482_ = lean_ctor_get(v_t_478_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v_t_478_, 1);
v___x_483_ = lean_apply_1(v_k_479_, v_val_482_);
return v___x_483_;
}
case 2:
{
lean_object* v_catName_484_; lean_object* v_declName_485_; uint8_t v_behavior_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_catName_484_ = lean_ctor_get(v_t_478_, 0);
lean_inc(v_catName_484_);
v_declName_485_ = lean_ctor_get(v_t_478_, 1);
lean_inc(v_declName_485_);
v_behavior_486_ = lean_ctor_get_uint8(v_t_478_, sizeof(void*)*2);
lean_dec_ref_known(v_t_478_, 2);
v___x_487_ = lean_box(v_behavior_486_);
v___x_488_ = lean_apply_3(v_k_479_, v_catName_484_, v_declName_485_, v___x_487_);
return v___x_488_;
}
default: 
{
lean_object* v_catName_489_; lean_object* v_declName_490_; lean_object* v_prio_491_; lean_object* v___x_492_; 
v_catName_489_ = lean_ctor_get(v_t_478_, 0);
lean_inc(v_catName_489_);
v_declName_490_ = lean_ctor_get(v_t_478_, 1);
lean_inc(v_declName_490_);
v_prio_491_ = lean_ctor_get(v_t_478_, 2);
lean_inc(v_prio_491_);
lean_dec_ref_known(v_t_478_, 3);
v___x_492_ = lean_apply_3(v_k_479_, v_catName_489_, v_declName_490_, v_prio_491_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_493_, lean_object* v_ctorIdx_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_k_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_495_, v_k_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_499_, lean_object* v_ctorIdx_500_, lean_object* v_t_501_, lean_object* v_h_502_, lean_object* v_k_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_499_, v_ctorIdx_500_, v_t_501_, v_h_502_, v_k_503_);
lean_dec(v_ctorIdx_500_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_505_, lean_object* v_token_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_505_, v_token_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_token_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_509_, v_token_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_513_, lean_object* v_kind_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_513_, v_kind_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_516_, lean_object* v_t_517_, lean_object* v_h_518_, lean_object* v_kind_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_517_, v_kind_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_521_, lean_object* v_category_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_521_, v_category_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_524_, lean_object* v_t_525_, lean_object* v_h_526_, lean_object* v_category_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_525_, v_category_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_529_, lean_object* v_parser_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_529_, v_parser_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_532_, lean_object* v_t_533_, lean_object* v_h_534_, lean_object* v_parser_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_533_, v_parser_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object* v_x_542_){
_start:
{
switch(lean_obj_tag(v_x_542_))
{
case 0:
{
lean_object* v___x_543_; 
v___x_543_ = lean_unsigned_to_nat(0u);
return v___x_543_;
}
case 1:
{
lean_object* v___x_544_; 
v___x_544_ = lean_unsigned_to_nat(1u);
return v___x_544_;
}
case 2:
{
lean_object* v___x_545_; 
v___x_545_ = lean_unsigned_to_nat(2u);
return v___x_545_;
}
default: 
{
lean_object* v___x_546_; 
v___x_546_ = lean_unsigned_to_nat(3u);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object* v_x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx(v_x_547_);
lean_dec_ref(v_x_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_549_, lean_object* v_k_550_){
_start:
{
switch(lean_obj_tag(v_t_549_))
{
case 0:
{
lean_object* v_val_551_; lean_object* v___x_552_; 
v_val_551_ = lean_ctor_get(v_t_549_, 0);
lean_inc_ref(v_val_551_);
lean_dec_ref_known(v_t_549_, 1);
v___x_552_ = lean_apply_1(v_k_550_, v_val_551_);
return v___x_552_;
}
case 1:
{
lean_object* v_val_553_; lean_object* v___x_554_; 
v_val_553_ = lean_ctor_get(v_t_549_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v_t_549_, 1);
v___x_554_ = lean_apply_1(v_k_550_, v_val_553_);
return v___x_554_;
}
case 2:
{
lean_object* v_catName_555_; lean_object* v_declName_556_; uint8_t v_behavior_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_catName_555_ = lean_ctor_get(v_t_549_, 0);
lean_inc(v_catName_555_);
v_declName_556_ = lean_ctor_get(v_t_549_, 1);
lean_inc(v_declName_556_);
v_behavior_557_ = lean_ctor_get_uint8(v_t_549_, sizeof(void*)*2);
lean_dec_ref_known(v_t_549_, 2);
v___x_558_ = lean_box(v_behavior_557_);
v___x_559_ = lean_apply_3(v_k_550_, v_catName_555_, v_declName_556_, v___x_558_);
return v___x_559_;
}
default: 
{
lean_object* v_catName_560_; lean_object* v_declName_561_; uint8_t v_leading_562_; lean_object* v_p_563_; lean_object* v_prio_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_catName_560_ = lean_ctor_get(v_t_549_, 0);
lean_inc(v_catName_560_);
v_declName_561_ = lean_ctor_get(v_t_549_, 1);
lean_inc(v_declName_561_);
v_leading_562_ = lean_ctor_get_uint8(v_t_549_, sizeof(void*)*4);
v_p_563_ = lean_ctor_get(v_t_549_, 2);
lean_inc_ref(v_p_563_);
v_prio_564_ = lean_ctor_get(v_t_549_, 3);
lean_inc(v_prio_564_);
lean_dec_ref_known(v_t_549_, 4);
v___x_565_ = lean_box(v_leading_562_);
v___x_566_ = lean_apply_5(v_k_550_, v_catName_560_, v_declName_561_, v___x_565_, v_p_563_, v_prio_564_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_567_, lean_object* v_ctorIdx_568_, lean_object* v_t_569_, lean_object* v_h_570_, lean_object* v_k_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_569_, v_k_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_573_, lean_object* v_ctorIdx_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_k_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_573_, v_ctorIdx_574_, v_t_575_, v_h_576_, v_k_577_);
lean_dec(v_ctorIdx_574_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_579_, lean_object* v_token_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_579_, v_token_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_582_, lean_object* v_t_583_, lean_object* v_h_584_, lean_object* v_token_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_583_, v_token_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_587_, lean_object* v_kind_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_587_, v_kind_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_kind_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_591_, v_kind_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_595_, lean_object* v_category_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_595_, v_category_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_category_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_599_, v_category_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_603_, lean_object* v_parser_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_603_, v_parser_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_606_, lean_object* v_t_607_, lean_object* v_h_608_, lean_object* v_parser_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_607_, v_parser_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_615_){
_start:
{
switch(lean_obj_tag(v_x_615_))
{
case 0:
{
lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_val_616_ = lean_ctor_get(v_x_615_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v_x_615_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_dec(v_x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
case 1:
{
lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
v_val_624_ = lean_ctor_get(v_x_615_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v_x_615_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v_x_615_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_val_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
case 2:
{
lean_object* v_catName_632_; lean_object* v_declName_633_; uint8_t v_behavior_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_catName_632_ = lean_ctor_get(v_x_615_, 0);
v_declName_633_ = lean_ctor_get(v_x_615_, 1);
v_behavior_634_ = lean_ctor_get_uint8(v_x_615_, sizeof(void*)*2);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v_x_615_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_declName_633_);
lean_inc(v_catName_632_);
lean_dec(v_x_615_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_catName_632_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_declName_633_);
lean_ctor_set_uint8(v_reuseFailAlloc_640_, sizeof(void*)*2, v_behavior_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
default: 
{
lean_object* v_catName_642_; lean_object* v_declName_643_; lean_object* v_prio_644_; lean_object* v___x_645_; 
v_catName_642_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_catName_642_);
v_declName_643_ = lean_ctor_get(v_x_615_, 1);
lean_inc(v_declName_643_);
v_prio_644_ = lean_ctor_get(v_x_615_, 3);
lean_inc(v_prio_644_);
lean_dec_ref_known(v_x_615_, 4);
v___x_645_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_645_, 0, v_catName_642_);
lean_ctor_set(v___x_645_, 1, v_declName_643_);
lean_ctor_set(v___x_645_, 2, v_prio_644_);
return v___x_645_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_647_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
lean_ctor_set(v___x_648_, 2, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_652_ = l_Lean_Parser_builtinTokenTable;
v___x_653_ = lean_st_ref_get(v___x_652_);
v___x_654_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_655_ = lean_st_ref_get(v___x_654_);
v___x_656_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_657_ = lean_st_ref_get(v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_658_, 0, v___x_653_);
lean_ctor_set(v___x_658_, 1, v___x_655_);
lean_ctor_set(v___x_658_, 2, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_665_, lean_object* v_tk_666_){
_start:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_668_ = lean_string_dec_eq(v_tk_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_665_, v_tk_666_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_inc_ref(v_tk_666_);
v___x_670_ = l_Lean_Data_Trie_insert___redArg(v_tokens_665_, v_tk_666_, v_tk_666_);
lean_dec_ref(v_tk_666_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
else
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_tk_666_);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v___x_669_, 0);
lean_dec(v_unused_679_);
v___x_673_ = v___x_669_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_dec(v___x_669_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_tokens_665_);
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_tokens_665_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v___x_680_; 
lean_dec_ref(v_tk_666_);
lean_dec_ref(v_tokens_665_);
v___x_680_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_683_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_684_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_685_ = 1;
v___x_686_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_683_, v___x_685_);
v___x_687_ = lean_string_append(v___x_684_, v___x_686_);
lean_dec_ref(v___x_686_);
v___x_688_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_691_, lean_object* v_catName_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_696_, lean_object* v_catName_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_699_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_700_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_698_, v___x_699_, v_categories_696_, v_catName_697_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_701_, lean_object* v_catName_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Parser_getCategory(v_categories_701_, v_catName_702_);
lean_dec_ref(v_categories_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_705_){
_start:
{
lean_object* v___f_706_; lean_object* v___x_707_; 
v___f_706_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_707_ = l_List_eraseDupsBy___redArg(v___f_706_, v_as_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_708_, lean_object* v_prio_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
lean_dec(v_prio_709_);
lean_dec_ref(v_p_708_);
return v_x_710_;
}
else
{
lean_object* v_head_712_; lean_object* v_tail_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_733_; 
v_head_712_ = lean_ctor_get(v_x_711_, 0);
v_tail_713_ = lean_ctor_get(v_x_711_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_733_ == 0)
{
v___x_715_ = v_x_711_;
v_isShared_716_ = v_isSharedCheck_733_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_tail_713_);
lean_inc(v_head_712_);
lean_dec(v_x_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_733_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_leadingTable_717_; lean_object* v_leadingParsers_718_; lean_object* v_trailingTable_719_; lean_object* v_trailingParsers_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_732_; 
v_leadingTable_717_ = lean_ctor_get(v_x_710_, 0);
v_leadingParsers_718_ = lean_ctor_get(v_x_710_, 1);
v_trailingTable_719_ = lean_ctor_get(v_x_710_, 2);
v_trailingParsers_720_ = lean_ctor_get(v_x_710_, 3);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_710_);
if (v_isSharedCheck_732_ == 0)
{
v___x_722_ = v_x_710_;
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_trailingParsers_720_);
lean_inc(v_trailingTable_719_);
lean_inc(v_leadingParsers_718_);
lean_inc(v_leadingTable_717_);
lean_dec(v_x_710_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_732_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
lean_inc(v_prio_709_);
lean_inc_ref(v_p_708_);
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 0);
lean_ctor_set(v___x_715_, 1, v_prio_709_);
lean_ctor_set(v___x_715_, 0, v_p_708_);
v___x_725_ = v___x_715_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_p_708_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_prio_709_);
v___x_725_ = v_reuseFailAlloc_731_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_717_, v_head_712_, v___x_725_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_leadingParsers_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_trailingTable_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_trailingParsers_720_);
v___x_728_ = v_reuseFailAlloc_730_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
v_x_710_ = v___x_728_;
v_x_711_ = v_tail_713_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_734_, lean_object* v_vals_735_, lean_object* v_i_736_, lean_object* v_k_737_){
_start:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_array_get_size(v_keys_734_);
v___x_739_ = lean_nat_dec_lt(v_i_736_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v_i_736_);
v___x_740_ = lean_box(0);
return v___x_740_;
}
else
{
lean_object* v_k_x27_741_; uint8_t v___x_742_; 
v_k_x27_741_ = lean_array_fget_borrowed(v_keys_734_, v_i_736_);
v___x_742_ = lean_name_eq(v_k_737_, v_k_x27_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_i_736_, v___x_743_);
lean_dec(v_i_736_);
v_i_736_ = v___x_744_;
goto _start;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_array_fget_borrowed(v_vals_735_, v_i_736_);
lean_dec(v_i_736_);
lean_inc(v___x_746_);
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_748_, lean_object* v_vals_749_, lean_object* v_i_750_, lean_object* v_k_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_748_, v_vals_749_, v_i_750_, v_k_751_);
lean_dec(v_k_751_);
lean_dec_ref(v_vals_749_);
lean_dec_ref(v_keys_748_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_753_, size_t v_x_754_, lean_object* v_x_755_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v_es_756_; lean_object* v___x_757_; size_t v___x_758_; size_t v___x_759_; lean_object* v_j_760_; lean_object* v___x_761_; 
v_es_756_ = lean_ctor_get(v_x_753_, 0);
v___x_757_ = lean_box(2);
v___x_758_ = ((size_t)31ULL);
v___x_759_ = lean_usize_land(v_x_754_, v___x_758_);
v_j_760_ = lean_usize_to_nat(v___x_759_);
v___x_761_ = lean_array_get_borrowed(v___x_757_, v_es_756_, v_j_760_);
lean_dec(v_j_760_);
switch(lean_obj_tag(v___x_761_))
{
case 0:
{
lean_object* v_key_762_; lean_object* v_val_763_; uint8_t v___x_764_; 
v_key_762_ = lean_ctor_get(v___x_761_, 0);
v_val_763_ = lean_ctor_get(v___x_761_, 1);
v___x_764_ = lean_name_eq(v_x_755_, v_key_762_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = lean_box(0);
return v___x_765_;
}
else
{
lean_object* v___x_766_; 
lean_inc(v_val_763_);
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_val_763_);
return v___x_766_;
}
}
case 1:
{
lean_object* v_node_767_; size_t v___x_768_; size_t v___x_769_; 
v_node_767_ = lean_ctor_get(v___x_761_, 0);
v___x_768_ = ((size_t)5ULL);
v___x_769_ = lean_usize_shift_right(v_x_754_, v___x_768_);
v_x_753_ = v_node_767_;
v_x_754_ = v___x_769_;
goto _start;
}
default: 
{
lean_object* v___x_771_; 
v___x_771_ = lean_box(0);
return v___x_771_;
}
}
}
else
{
lean_object* v_ks_772_; lean_object* v_vs_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_ks_772_ = lean_ctor_get(v_x_753_, 0);
v_vs_773_ = lean_ctor_get(v_x_753_, 1);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_772_, v_vs_773_, v___x_774_, v_x_755_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
size_t v_x_492__boxed_779_; lean_object* v_res_780_; 
v_x_492__boxed_779_ = lean_unbox_usize(v_x_777_);
lean_dec(v_x_777_);
v_res_780_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_776_, v_x_492__boxed_779_, v_x_778_);
lean_dec(v_x_778_);
lean_dec_ref(v_x_776_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
uint64_t v___y_784_; 
if (lean_obj_tag(v_x_782_) == 0)
{
uint64_t v___x_787_; 
v___x_787_ = 1723ULL;
v___y_784_ = v___x_787_;
goto v___jp_783_;
}
else
{
uint64_t v_hash_788_; 
v_hash_788_ = lean_ctor_get_uint64(v_x_782_, sizeof(void*)*2);
v___y_784_ = v_hash_788_;
goto v___jp_783_;
}
v___jp_783_:
{
size_t v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_uint64_to_usize(v___y_784_);
v___x_786_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_781_, v___x_785_, v_x_782_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec_ref(v_x_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
if (lean_obj_tag(v_a_792_) == 0)
{
lean_object* v___x_794_; 
v___x_794_ = l_List_reverse___redArg(v_a_793_);
return v___x_794_;
}
else
{
lean_object* v_head_795_; lean_object* v_tail_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_806_; 
v_head_795_ = lean_ctor_get(v_a_792_, 0);
v_tail_796_ = lean_ctor_get(v_a_792_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_a_792_);
if (v_isSharedCheck_806_ == 0)
{
v___x_798_ = v_a_792_;
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_tail_796_);
lean_inc(v_head_795_);
lean_dec(v_a_792_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_800_ = lean_box(0);
v___x_801_ = l_Lean_Name_str___override(v___x_800_, v_head_795_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v_a_793_);
lean_ctor_set(v___x_798_, 0, v___x_801_);
v___x_803_ = v___x_798_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_a_793_);
v___x_803_ = v_reuseFailAlloc_805_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v_a_792_ = v_tail_796_;
v_a_793_ = v___x_803_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_807_, lean_object* v_catName_808_, lean_object* v_declName_809_, lean_object* v_p_810_, lean_object* v_prio_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_807_, v_catName_808_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; 
lean_dec(v_prio_811_);
lean_dec_ref(v_p_810_);
lean_dec(v_declName_809_);
lean_dec_ref(v_categories_807_);
v___x_813_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_808_);
return v___x_813_;
}
else
{
lean_object* v_val_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_860_; 
v_val_814_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_860_ == 0)
{
v___x_816_ = v___x_812_;
v_isShared_817_ = v_isSharedCheck_860_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_val_814_);
lean_dec(v___x_812_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_860_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_info_818_; lean_object* v_declName_819_; lean_object* v_kinds_820_; lean_object* v_tables_821_; uint8_t v_behavior_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_859_; 
v_info_818_ = lean_ctor_get(v_p_810_, 0);
v_declName_819_ = lean_ctor_get(v_val_814_, 0);
v_kinds_820_ = lean_ctor_get(v_val_814_, 1);
v_tables_821_ = lean_ctor_get(v_val_814_, 2);
v_behavior_822_ = lean_ctor_get_uint8(v_val_814_, sizeof(void*)*3);
v_isSharedCheck_859_ = !lean_is_exclusive(v_val_814_);
if (v_isSharedCheck_859_ == 0)
{
v___x_824_ = v_val_814_;
v_isShared_825_ = v_isSharedCheck_859_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_tables_821_);
lean_inc(v_kinds_820_);
lean_inc(v_declName_819_);
lean_dec(v_val_814_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_859_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_firstTokens_826_; lean_object* v_kinds_827_; lean_object* v_tks_829_; 
v_firstTokens_826_ = lean_ctor_get(v_info_818_, 2);
v_kinds_827_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_820_, v_declName_809_);
switch(lean_obj_tag(v_firstTokens_826_))
{
case 2:
{
lean_object* v_a_841_; 
v_a_841_ = lean_ctor_get(v_firstTokens_826_, 0);
lean_inc(v_a_841_);
v_tks_829_ = v_a_841_;
goto v___jp_828_;
}
case 3:
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v_firstTokens_826_, 0);
lean_inc(v_a_842_);
v_tks_829_ = v_a_842_;
goto v___jp_828_;
}
default: 
{
lean_object* v_leadingTable_843_; lean_object* v_leadingParsers_844_; lean_object* v_trailingTable_845_; lean_object* v_trailingParsers_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_858_; 
lean_del_object(v___x_824_);
lean_del_object(v___x_816_);
v_leadingTable_843_ = lean_ctor_get(v_tables_821_, 0);
v_leadingParsers_844_ = lean_ctor_get(v_tables_821_, 1);
v_trailingTable_845_ = lean_ctor_get(v_tables_821_, 2);
v_trailingParsers_846_ = lean_ctor_get(v_tables_821_, 3);
v_isSharedCheck_858_ = !lean_is_exclusive(v_tables_821_);
if (v_isSharedCheck_858_ == 0)
{
v___x_848_ = v_tables_821_;
v_isShared_849_ = v_isSharedCheck_858_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_trailingParsers_846_);
lean_inc(v_trailingTable_845_);
lean_inc(v_leadingParsers_844_);
lean_inc(v_leadingTable_843_);
lean_dec(v_tables_821_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_858_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_tables_853_; 
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_p_810_);
lean_ctor_set(v___x_850_, 1, v_prio_811_);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_leadingParsers_844_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v___x_851_);
v_tables_853_ = v___x_848_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_leadingTable_843_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_trailingTable_845_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_trailingParsers_846_);
v_tables_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_854_, 0, v_declName_819_);
lean_ctor_set(v___x_854_, 1, v_kinds_827_);
lean_ctor_set(v___x_854_, 2, v_tables_853_);
lean_ctor_set_uint8(v___x_854_, sizeof(void*)*3, v_behavior_822_);
v___x_855_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_807_, v_catName_808_, v___x_854_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
}
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v_tks_831_; lean_object* v___x_832_; lean_object* v_tables_833_; lean_object* v___x_835_; 
v___x_830_ = lean_box(0);
v_tks_831_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_829_, v___x_830_);
v___x_832_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_831_);
v_tables_833_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_810_, v_prio_811_, v_tables_821_, v___x_832_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 2, v_tables_833_);
lean_ctor_set(v___x_824_, 1, v_kinds_827_);
v___x_835_ = v___x_824_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_declName_819_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_kinds_827_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_tables_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*3, v_behavior_822_);
v___x_835_ = v_reuseFailAlloc_840_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_807_, v_catName_808_, v___x_835_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_836_);
v___x_838_ = v___x_816_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_865_, v_x_866_, v_x_867_);
lean_dec(v_x_867_);
lean_dec_ref(v_x_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_869_, lean_object* v_x_870_, size_t v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_870_, v_x_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
size_t v_x_661__boxed_878_; lean_object* v_res_879_; 
v_x_661__boxed_878_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_res_879_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_874_, v_x_875_, v_x_661__boxed_878_, v_x_877_);
lean_dec(v_x_877_);
lean_dec_ref(v_x_875_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_880_, lean_object* v_keys_881_, lean_object* v_vals_882_, lean_object* v_heq_883_, lean_object* v_i_884_, lean_object* v_k_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_881_, v_vals_882_, v_i_884_, v_k_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_887_, lean_object* v_keys_888_, lean_object* v_vals_889_, lean_object* v_heq_890_, lean_object* v_i_891_, lean_object* v_k_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_887_, v_keys_888_, v_vals_889_, v_heq_890_, v_i_891_, v_k_892_);
lean_dec(v_k_892_);
lean_dec_ref(v_vals_889_);
lean_dec_ref(v_keys_888_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_894_, lean_object* v_prio_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_dec(v_prio_895_);
lean_dec_ref(v_p_894_);
return v_x_896_;
}
else
{
lean_object* v_head_898_; lean_object* v_tail_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_919_; 
v_head_898_ = lean_ctor_get(v_x_897_, 0);
v_tail_899_ = lean_ctor_get(v_x_897_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_x_897_);
if (v_isSharedCheck_919_ == 0)
{
v___x_901_ = v_x_897_;
v_isShared_902_ = v_isSharedCheck_919_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_tail_899_);
lean_inc(v_head_898_);
lean_dec(v_x_897_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_919_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_leadingTable_903_; lean_object* v_leadingParsers_904_; lean_object* v_trailingTable_905_; lean_object* v_trailingParsers_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_918_; 
v_leadingTable_903_ = lean_ctor_get(v_x_896_, 0);
v_leadingParsers_904_ = lean_ctor_get(v_x_896_, 1);
v_trailingTable_905_ = lean_ctor_get(v_x_896_, 2);
v_trailingParsers_906_ = lean_ctor_get(v_x_896_, 3);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_896_);
if (v_isSharedCheck_918_ == 0)
{
v___x_908_ = v_x_896_;
v_isShared_909_ = v_isSharedCheck_918_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_trailingParsers_906_);
lean_inc(v_trailingTable_905_);
lean_inc(v_leadingParsers_904_);
lean_inc(v_leadingTable_903_);
lean_dec(v_x_896_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_918_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
lean_inc(v_prio_895_);
lean_inc_ref(v_p_894_);
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 0);
lean_ctor_set(v___x_901_, 1, v_prio_895_);
lean_ctor_set(v___x_901_, 0, v_p_894_);
v___x_911_ = v___x_901_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_p_894_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_prio_895_);
v___x_911_ = v_reuseFailAlloc_917_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_905_, v_head_898_, v___x_911_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 2, v___x_912_);
v___x_914_ = v___x_908_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_leadingTable_903_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_leadingParsers_904_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_trailingParsers_906_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
v_x_896_ = v___x_914_;
v_x_897_ = v_tail_899_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_920_, lean_object* v_p_921_, lean_object* v_prio_922_){
_start:
{
lean_object* v_tks_924_; lean_object* v_info_929_; lean_object* v_firstTokens_930_; 
v_info_929_ = lean_ctor_get(v_p_921_, 0);
v_firstTokens_930_ = lean_ctor_get(v_info_929_, 2);
switch(lean_obj_tag(v_firstTokens_930_))
{
case 2:
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v_firstTokens_930_, 0);
lean_inc(v_a_931_);
v_tks_924_ = v_a_931_;
goto v___jp_923_;
}
case 3:
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v_firstTokens_930_, 0);
lean_inc(v_a_932_);
v_tks_924_ = v_a_932_;
goto v___jp_923_;
}
default: 
{
lean_object* v_leadingTable_933_; lean_object* v_leadingParsers_934_; lean_object* v_trailingTable_935_; lean_object* v_trailingParsers_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_945_; 
v_leadingTable_933_ = lean_ctor_get(v_tables_920_, 0);
v_leadingParsers_934_ = lean_ctor_get(v_tables_920_, 1);
v_trailingTable_935_ = lean_ctor_get(v_tables_920_, 2);
v_trailingParsers_936_ = lean_ctor_get(v_tables_920_, 3);
v_isSharedCheck_945_ = !lean_is_exclusive(v_tables_920_);
if (v_isSharedCheck_945_ == 0)
{
v___x_938_ = v_tables_920_;
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_trailingParsers_936_);
lean_inc(v_trailingTable_935_);
lean_inc(v_leadingParsers_934_);
lean_inc(v_leadingTable_933_);
lean_dec(v_tables_920_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_p_921_);
lean_ctor_set(v___x_940_, 1, v_prio_922_);
v___x_941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v_trailingParsers_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 3, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_leadingTable_933_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_leadingParsers_934_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_trailingTable_935_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
v___jp_923_:
{
lean_object* v___x_925_; lean_object* v_tks_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_box(0);
v_tks_926_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_924_, v___x_925_);
v___x_927_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_926_);
v___x_928_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_921_, v_prio_922_, v_tables_920_, v___x_927_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_946_, lean_object* v_catName_947_, lean_object* v_declName_948_, lean_object* v_p_949_, lean_object* v_prio_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_946_, v_catName_947_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v___x_952_; 
lean_dec(v_prio_950_);
lean_dec_ref(v_p_949_);
lean_dec(v_declName_948_);
lean_dec_ref(v_categories_946_);
v___x_952_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_947_);
return v___x_952_;
}
else
{
lean_object* v_val_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_974_; 
v_val_953_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_974_ == 0)
{
v___x_955_ = v___x_951_;
v_isShared_956_ = v_isSharedCheck_974_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_val_953_);
lean_dec(v___x_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_974_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_declName_957_; lean_object* v_kinds_958_; lean_object* v_tables_959_; uint8_t v_behavior_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_973_; 
v_declName_957_ = lean_ctor_get(v_val_953_, 0);
v_kinds_958_ = lean_ctor_get(v_val_953_, 1);
v_tables_959_ = lean_ctor_get(v_val_953_, 2);
v_behavior_960_ = lean_ctor_get_uint8(v_val_953_, sizeof(void*)*3);
v_isSharedCheck_973_ = !lean_is_exclusive(v_val_953_);
if (v_isSharedCheck_973_ == 0)
{
v___x_962_ = v_val_953_;
v_isShared_963_ = v_isSharedCheck_973_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_tables_959_);
lean_inc(v_kinds_958_);
lean_inc(v_declName_957_);
lean_dec(v_val_953_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_973_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_kinds_964_; lean_object* v_tables_965_; lean_object* v___x_967_; 
v_kinds_964_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_958_, v_declName_948_);
v_tables_965_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_959_, v_p_949_, v_prio_950_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 2, v_tables_965_);
lean_ctor_set(v___x_962_, 1, v_kinds_964_);
v___x_967_ = v___x_962_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_declName_957_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_kinds_964_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_tables_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3, v_behavior_960_);
v___x_967_ = v_reuseFailAlloc_972_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_946_, v_catName_947_, v___x_967_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_968_);
v___x_970_ = v___x_955_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_975_, lean_object* v_catName_976_, lean_object* v_declName_977_, uint8_t v_leading_978_, lean_object* v_p_979_, lean_object* v_prio_980_){
_start:
{
if (v_leading_978_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Parser_addTrailingParser(v_categories_975_, v_catName_976_, v_declName_977_, v_p_979_, v_prio_980_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Parser_addLeadingParser(v_categories_975_, v_catName_976_, v_declName_977_, v_p_979_, v_prio_980_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_983_, lean_object* v_catName_984_, lean_object* v_declName_985_, lean_object* v_leading_986_, lean_object* v_p_987_, lean_object* v_prio_988_){
_start:
{
uint8_t v_leading_boxed_989_; lean_object* v_res_990_; 
v_leading_boxed_989_ = lean_unbox(v_leading_986_);
v_res_990_ = l_Lean_Parser_addParser(v_categories_983_, v_catName_984_, v_declName_985_, v_leading_boxed_989_, v_p_987_, v_prio_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v_x_991_);
return v___x_993_;
}
else
{
lean_object* v_head_994_; lean_object* v_tail_995_; lean_object* v___x_996_; 
v_head_994_ = lean_ctor_get(v_x_992_, 0);
lean_inc(v_head_994_);
v_tail_995_ = lean_ctor_get(v_x_992_, 1);
lean_inc(v_tail_995_);
lean_dec_ref_known(v_x_992_, 2);
v___x_996_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_991_, v_head_994_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_dec(v_tail_995_);
return v___x_996_;
}
else
{
lean_object* v_a_997_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v_x_991_ = v_a_997_;
v_x_992_ = v_tail_995_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_999_, lean_object* v_info_1000_){
_start:
{
lean_object* v_collectTokens_1001_; lean_object* v___x_1002_; lean_object* v_newTokens_1003_; lean_object* v___x_1004_; 
v_collectTokens_1001_ = lean_ctor_get(v_info_1000_, 0);
lean_inc_ref(v_collectTokens_1001_);
lean_dec_ref(v_info_1000_);
v___x_1002_ = lean_box(0);
v_newTokens_1003_ = lean_apply_1(v_collectTokens_1001_, v___x_1002_);
v___x_1004_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_999_, v_newTokens_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_1007_, lean_object* v_declName_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1010_ = l_Lean_Parser_builtinTokenTable;
v___x_1011_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_1012_ = lean_st_ref_swap(v___x_1010_, v___x_1011_);
v___x_1013_ = l_Lean_Parser_addParserTokens(v___x_1012_, v_info_1007_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1030_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1030_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1030_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1019_ = l_Lean_privateToUserName(v_declName_1008_);
v___x_1020_ = 1;
v___x_1021_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1019_, v___x_1020_);
v___x_1022_ = lean_string_append(v___x_1018_, v___x_1021_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1024_ = lean_string_append(v___x_1022_, v___x_1023_);
v___x_1025_ = lean_string_append(v___x_1024_, v_a_1014_);
lean_dec(v_a_1014_);
v___x_1026_ = lean_mk_io_user_error(v___x_1025_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1026_);
v___x_1028_ = v___x_1016_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_declName_1008_);
v_a_1031_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1033_ = v___x_1013_;
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1013_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1035_ = lean_st_ref_swap(v___x_1010_, v_a_1031_);
lean_dec(v___x_1035_);
v___x_1036_ = lean_box(0);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1036_);
v___x_1038_ = v___x_1033_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1041_, lean_object* v_declName_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1041_, v_declName_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1045_){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1047_ = lean_panic_fn_borrowed(v___x_1046_, v_msg_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1051_, lean_object* v_e_1052_){
_start:
{
switch(lean_obj_tag(v_e_1052_))
{
case 0:
{
lean_object* v_val_1053_; lean_object* v_tokens_1054_; lean_object* v_kinds_1055_; lean_object* v_categories_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1074_; 
v_val_1053_ = lean_ctor_get(v_e_1052_, 0);
lean_inc_ref(v_val_1053_);
lean_dec_ref_known(v_e_1052_, 1);
v_tokens_1054_ = lean_ctor_get(v_s_1051_, 0);
v_kinds_1055_ = lean_ctor_get(v_s_1051_, 1);
v_categories_1056_ = lean_ctor_get(v_s_1051_, 2);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_s_1051_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1058_ = v_s_1051_;
v_isShared_1059_ = v_isSharedCheck_1074_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_categories_1056_);
lean_inc(v_kinds_1055_);
lean_inc(v_tokens_1054_);
lean_dec(v_s_1051_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1074_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1054_, v_val_1053_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_del_object(v___x_1058_);
lean_dec_ref(v_categories_1056_);
lean_dec_ref(v_kinds_1055_);
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v___x_1062_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1063_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1064_ = lean_unsigned_to_nat(166u);
v___x_1065_ = lean_unsigned_to_nat(26u);
v___x_1066_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1067_ = lean_string_append(v___x_1066_, v_a_1061_);
lean_dec(v_a_1061_);
v___x_1068_ = l_mkPanicMessageWithDecl(v___x_1062_, v___x_1063_, v___x_1064_, v___x_1065_, v___x_1067_);
lean_dec_ref(v___x_1067_);
v___x_1069_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1068_);
return v___x_1069_;
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; 
v_a_1070_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1060_, 1);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_a_1070_);
v___x_1072_ = v___x_1058_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1070_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_kinds_1055_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_categories_1056_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
case 1:
{
lean_object* v_val_1075_; lean_object* v_tokens_1076_; lean_object* v_kinds_1077_; lean_object* v_categories_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v_val_1075_ = lean_ctor_get(v_e_1052_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v_e_1052_, 1);
v_tokens_1076_ = lean_ctor_get(v_s_1051_, 0);
v_kinds_1077_ = lean_ctor_get(v_s_1051_, 1);
v_categories_1078_ = lean_ctor_get(v_s_1051_, 2);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_s_1051_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v_s_1051_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_categories_1078_);
lean_inc(v_kinds_1077_);
lean_inc(v_tokens_1076_);
lean_dec(v_s_1051_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1077_, v_val_1075_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_tokens_1076_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_categories_1078_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
case 2:
{
lean_object* v_catName_1087_; lean_object* v_declName_1088_; uint8_t v_behavior_1089_; lean_object* v_tokens_1090_; lean_object* v_kinds_1091_; lean_object* v_categories_1092_; uint8_t v___x_1093_; 
v_catName_1087_ = lean_ctor_get(v_e_1052_, 0);
lean_inc(v_catName_1087_);
v_declName_1088_ = lean_ctor_get(v_e_1052_, 1);
lean_inc(v_declName_1088_);
v_behavior_1089_ = lean_ctor_get_uint8(v_e_1052_, sizeof(void*)*2);
lean_dec_ref_known(v_e_1052_, 2);
v_tokens_1090_ = lean_ctor_get(v_s_1051_, 0);
v_kinds_1091_ = lean_ctor_get(v_s_1051_, 1);
v_categories_1092_ = lean_ctor_get(v_s_1051_, 2);
v___x_1093_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1092_, v_catName_1087_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1104_; 
lean_inc_ref(v_categories_1092_);
lean_inc_ref(v_kinds_1091_);
lean_inc_ref(v_tokens_1090_);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_s_1051_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; lean_object* v_unused_1106_; lean_object* v_unused_1107_; 
v_unused_1105_ = lean_ctor_get(v_s_1051_, 2);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_s_1051_, 1);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_s_1051_, 0);
lean_dec(v_unused_1107_);
v___x_1095_ = v_s_1051_;
v_isShared_1096_ = v_isSharedCheck_1104_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v_s_1051_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1104_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1097_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1098_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1099_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1099_, 0, v_declName_1088_);
lean_ctor_set(v___x_1099_, 1, v___x_1097_);
lean_ctor_set(v___x_1099_, 2, v___x_1098_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*3, v_behavior_1089_);
v___x_1100_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1092_, v_catName_1087_, v___x_1099_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 2, v___x_1100_);
v___x_1102_ = v___x_1095_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_tokens_1090_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_kinds_1091_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
else
{
lean_dec(v_declName_1088_);
lean_dec(v_catName_1087_);
return v_s_1051_;
}
}
default: 
{
lean_object* v_catName_1108_; lean_object* v_declName_1109_; uint8_t v_leading_1110_; lean_object* v_p_1111_; lean_object* v_prio_1112_; lean_object* v_tokens_1113_; lean_object* v_kinds_1114_; lean_object* v_categories_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1133_; 
v_catName_1108_ = lean_ctor_get(v_e_1052_, 0);
lean_inc(v_catName_1108_);
v_declName_1109_ = lean_ctor_get(v_e_1052_, 1);
lean_inc(v_declName_1109_);
v_leading_1110_ = lean_ctor_get_uint8(v_e_1052_, sizeof(void*)*4);
v_p_1111_ = lean_ctor_get(v_e_1052_, 2);
lean_inc_ref(v_p_1111_);
v_prio_1112_ = lean_ctor_get(v_e_1052_, 3);
lean_inc(v_prio_1112_);
lean_dec_ref_known(v_e_1052_, 4);
v_tokens_1113_ = lean_ctor_get(v_s_1051_, 0);
v_kinds_1114_ = lean_ctor_get(v_s_1051_, 1);
v_categories_1115_ = lean_ctor_get(v_s_1051_, 2);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_s_1051_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1117_ = v_s_1051_;
v_isShared_1118_ = v_isSharedCheck_1133_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_categories_1115_);
lean_inc(v_kinds_1114_);
lean_inc(v_tokens_1113_);
lean_dec(v_s_1051_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1133_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Parser_addParser(v_categories_1115_, v_catName_1108_, v_declName_1109_, v_leading_1110_, v_p_1111_, v_prio_1112_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_del_object(v___x_1117_);
lean_dec_ref(v_kinds_1114_);
lean_dec_ref(v_tokens_1113_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1122_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1123_ = lean_unsigned_to_nat(176u);
v___x_1124_ = lean_unsigned_to_nat(30u);
v___x_1125_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1126_ = lean_string_append(v___x_1125_, v_a_1120_);
lean_dec(v_a_1120_);
v___x_1127_ = l_mkPanicMessageWithDecl(v___x_1121_, v___x_1122_, v___x_1123_, v___x_1124_, v___x_1126_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1127_);
return v___x_1128_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; 
v_a_1129_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1119_, 1);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 2, v_a_1129_);
v___x_1131_ = v___x_1117_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_tokens_1113_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_kinds_1114_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_a_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg(lean_object* v_x_1134_){
_start:
{
switch(lean_obj_tag(v_x_1134_))
{
case 0:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
return v___x_1135_;
}
case 1:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_unsigned_to_nat(1u);
return v___x_1136_;
}
default: 
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_unsigned_to_nat(2u);
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg___boxed(lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1138_);
lean_dec_ref(v_x_1138_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx(lean_object* v_00_u03b1_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Parser_AliasValue_ctorIdx(v_00_u03b1_1143_, v_x_1144_);
lean_dec_ref(v_x_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_1146_, lean_object* v_k_1147_){
_start:
{
lean_object* v_p_1148_; lean_object* v___x_1149_; 
v_p_1148_ = lean_ctor_get(v_t_1146_, 0);
lean_inc(v_p_1148_);
lean_dec_ref(v_t_1146_);
v___x_1149_ = lean_apply_1(v_k_1147_, v_p_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_1150_, lean_object* v_motive_1151_, lean_object* v_ctorIdx_1152_, lean_object* v_t_1153_, lean_object* v_h_1154_, lean_object* v_k_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1153_, v_k_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_1157_, lean_object* v_motive_1158_, lean_object* v_ctorIdx_1159_, lean_object* v_t_1160_, lean_object* v_h_1161_, lean_object* v_k_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_1157_, v_motive_1158_, v_ctorIdx_1159_, v_t_1160_, v_h_1161_, v_k_1162_);
lean_dec(v_ctorIdx_1159_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_1164_, lean_object* v_const_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1164_, v_const_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_1167_, lean_object* v_motive_1168_, lean_object* v_t_1169_, lean_object* v_h_1170_, lean_object* v_const_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1169_, v_const_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_1173_, lean_object* v_unary_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1173_, v_unary_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_1176_, lean_object* v_motive_1177_, lean_object* v_t_1178_, lean_object* v_h_1179_, lean_object* v_unary_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1178_, v_unary_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_1182_, lean_object* v_binary_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1182_, v_binary_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_1185_, lean_object* v_motive_1186_, lean_object* v_t_1187_, lean_object* v_h_1188_, lean_object* v_binary_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1187_, v_binary_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__0));
v___x_1193_ = lean_mk_io_user_error(v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object* v_mapRef_1196_, lean_object* v_aliasName_1197_, lean_object* v_value_1198_){
_start:
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_initializing();
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec_ref(v_value_1198_);
lean_dec(v_aliasName_1197_);
v___x_1201_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_st_ref_get(v_mapRef_1196_);
v___x_1204_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1197_, v___x_1203_);
lean_dec(v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1205_ = lean_st_ref_take(v_mapRef_1196_);
v___x_1206_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1197_, v_value_1198_, v___x_1205_);
v___x_1207_ = lean_st_ref_put(v_mapRef_1196_, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec_ref(v_value_1198_);
v___x_1209_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1210_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1197_, v___x_1204_);
v___x_1211_ = lean_string_append(v___x_1209_, v___x_1210_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1213_ = lean_string_append(v___x_1211_, v___x_1212_);
v___x_1214_ = lean_mk_io_user_error(v___x_1213_);
v___x_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1216_, lean_object* v_aliasName_1217_, lean_object* v_value_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1216_, v_aliasName_1217_, v_value_1218_);
lean_dec(v_mapRef_1216_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1221_, lean_object* v_mapRef_1222_, lean_object* v_aliasName_1223_, lean_object* v_value_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1222_, v_aliasName_1223_, v_value_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_mapRef_1228_, lean_object* v_aliasName_1229_, lean_object* v_value_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Parser_registerAliasCore(v_00_u03b1_1227_, v_mapRef_1228_, v_aliasName_1229_, v_value_1230_);
lean_dec(v_mapRef_1228_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1233_, lean_object* v_aliasName_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_st_ref_get(v_mapRef_1233_);
v___x_1237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1236_, v_aliasName_1234_);
lean_dec(v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1239_, lean_object* v_aliasName_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1239_, v_aliasName_1240_);
lean_dec(v_aliasName_1240_);
lean_dec(v_mapRef_1239_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1243_, lean_object* v_mapRef_1244_, lean_object* v_aliasName_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1244_, v_aliasName_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_mapRef_1249_, lean_object* v_aliasName_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Parser_getAlias(v_00_u03b1_1248_, v_mapRef_1249_, v_aliasName_1250_);
lean_dec(v_aliasName_1250_);
lean_dec(v_mapRef_1249_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1257_, lean_object* v_aliasName_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1300_; 
v___x_1260_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1257_, v_aliasName_1258_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1300_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1300_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
if (lean_obj_tag(v_a_1261_) == 0)
{
lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1265_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1266_ = 1;
v___x_1267_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1258_, v___x_1266_);
v___x_1268_ = lean_string_append(v___x_1265_, v___x_1267_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1270_ = lean_string_append(v___x_1268_, v___x_1269_);
v___x_1271_ = lean_mk_io_user_error(v___x_1270_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 1);
lean_ctor_set(v___x_1263_, 0, v___x_1271_);
v___x_1273_ = v___x_1263_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
else
{
lean_object* v_val_1275_; 
v_val_1275_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_val_1275_);
lean_dec_ref_known(v_a_1261_, 1);
switch(lean_obj_tag(v_val_1275_))
{
case 0:
{
lean_object* v_p_1276_; lean_object* v___x_1278_; 
lean_dec(v_aliasName_1258_);
v_p_1276_ = lean_ctor_get(v_val_1275_, 0);
lean_inc(v_p_1276_);
lean_dec_ref_known(v_val_1275_, 1);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v_p_1276_);
v___x_1278_ = v___x_1263_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_p_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
case 1:
{
lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_dec_ref_known(v_val_1275_, 1);
v___x_1280_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1281_ = 1;
v___x_1282_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1258_, v___x_1281_);
v___x_1283_ = lean_string_append(v___x_1280_, v___x_1282_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1285_ = lean_string_append(v___x_1283_, v___x_1284_);
v___x_1286_ = lean_mk_io_user_error(v___x_1285_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 1);
lean_ctor_set(v___x_1263_, 0, v___x_1286_);
v___x_1288_ = v___x_1263_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
default: 
{
lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_dec_ref_known(v_val_1275_, 1);
v___x_1290_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1291_ = 1;
v___x_1292_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1258_, v___x_1291_);
v___x_1293_ = lean_string_append(v___x_1290_, v___x_1292_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1295_ = lean_string_append(v___x_1293_, v___x_1294_);
v___x_1296_ = lean_mk_io_user_error(v___x_1295_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 1);
lean_ctor_set(v___x_1263_, 0, v___x_1296_);
v___x_1298_ = v___x_1263_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1301_, lean_object* v_aliasName_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1301_, v_aliasName_1302_);
lean_dec(v_mapRef_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1305_, lean_object* v_mapRef_1306_, lean_object* v_aliasName_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1306_, v_aliasName_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1310_, lean_object* v_mapRef_1311_, lean_object* v_aliasName_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1310_, v_mapRef_1311_, v_aliasName_1312_);
lean_dec(v_mapRef_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1316_, lean_object* v_aliasName_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1349_; 
v___x_1319_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1316_, v_aliasName_1317_);
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1349_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1349_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
if (lean_obj_tag(v_a_1320_) == 0)
{
lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1324_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1325_ = 1;
v___x_1326_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1317_, v___x_1325_);
v___x_1327_ = lean_string_append(v___x_1324_, v___x_1326_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1329_ = lean_string_append(v___x_1327_, v___x_1328_);
v___x_1330_ = lean_mk_io_user_error(v___x_1329_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 1);
lean_ctor_set(v___x_1322_, 0, v___x_1330_);
v___x_1332_ = v___x_1322_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_object* v_val_1334_; 
v_val_1334_ = lean_ctor_get(v_a_1320_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v_a_1320_, 1);
if (lean_obj_tag(v_val_1334_) == 1)
{
lean_object* v_p_1335_; lean_object* v___x_1337_; 
lean_dec(v_aliasName_1317_);
v_p_1335_ = lean_ctor_get(v_val_1334_, 0);
lean_inc(v_p_1335_);
lean_dec_ref_known(v_val_1334_, 1);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v_p_1335_);
v___x_1337_ = v___x_1322_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_p_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
lean_dec(v_val_1334_);
v___x_1339_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1340_ = 1;
v___x_1341_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1317_, v___x_1340_);
v___x_1342_ = lean_string_append(v___x_1339_, v___x_1341_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1344_ = lean_string_append(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_mk_io_user_error(v___x_1344_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 1);
lean_ctor_set(v___x_1322_, 0, v___x_1345_);
v___x_1347_ = v___x_1322_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1350_, lean_object* v_aliasName_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1350_, v_aliasName_1351_);
lean_dec(v_mapRef_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1354_, lean_object* v_mapRef_1355_, lean_object* v_aliasName_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1355_, v_aliasName_1356_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1359_, lean_object* v_mapRef_1360_, lean_object* v_aliasName_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1359_, v_mapRef_1360_, v_aliasName_1361_);
lean_dec(v_mapRef_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1365_, lean_object* v_aliasName_1366_){
_start:
{
lean_object* v___x_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1398_; 
v___x_1368_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1365_, v_aliasName_1366_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1398_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1398_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
if (lean_obj_tag(v_a_1369_) == 0)
{
lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1373_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1374_ = 1;
v___x_1375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1366_, v___x_1374_);
v___x_1376_ = lean_string_append(v___x_1373_, v___x_1375_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_mk_io_user_error(v___x_1378_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 1);
lean_ctor_set(v___x_1371_, 0, v___x_1379_);
v___x_1381_ = v___x_1371_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
else
{
lean_object* v_val_1383_; 
v_val_1383_ = lean_ctor_get(v_a_1369_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_a_1369_, 1);
if (lean_obj_tag(v_val_1383_) == 2)
{
lean_object* v_p_1384_; lean_object* v___x_1386_; 
lean_dec(v_aliasName_1366_);
v_p_1384_ = lean_ctor_get(v_val_1383_, 0);
lean_inc(v_p_1384_);
lean_dec_ref_known(v_val_1383_, 1);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_p_1384_);
v___x_1386_ = v___x_1371_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_p_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
else
{
lean_object* v___x_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_dec(v_val_1383_);
v___x_1388_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1389_ = 1;
v___x_1390_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1366_, v___x_1389_);
v___x_1391_ = lean_string_append(v___x_1388_, v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
v___x_1394_ = lean_mk_io_user_error(v___x_1393_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 1);
lean_ctor_set(v___x_1371_, 0, v___x_1394_);
v___x_1396_ = v___x_1371_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1399_, lean_object* v_aliasName_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1399_, v_aliasName_1400_);
lean_dec(v_mapRef_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1403_, lean_object* v_mapRef_1404_, lean_object* v_aliasName_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1404_, v_aliasName_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1408_, lean_object* v_mapRef_1409_, lean_object* v_aliasName_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1408_, v_mapRef_1409_, v_aliasName_1410_);
lean_dec(v_mapRef_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = lean_box(1);
v___x_1415_ = lean_st_mk_ref(v___x_1414_);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = lean_box(1);
v___x_1421_ = lean_st_mk_ref(v___x_1420_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_box(1);
v___x_1427_ = lean_st_mk_ref(v___x_1426_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1431_, lean_object* v_k_1432_, lean_object* v_fallback_1433_){
_start:
{
if (lean_obj_tag(v_t_1431_) == 0)
{
lean_object* v_k_1434_; lean_object* v_v_1435_; lean_object* v_l_1436_; lean_object* v_r_1437_; uint8_t v___x_1438_; 
v_k_1434_ = lean_ctor_get(v_t_1431_, 1);
v_v_1435_ = lean_ctor_get(v_t_1431_, 2);
v_l_1436_ = lean_ctor_get(v_t_1431_, 3);
v_r_1437_ = lean_ctor_get(v_t_1431_, 4);
v___x_1438_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1432_, v_k_1434_);
switch(v___x_1438_)
{
case 0:
{
v_t_1431_ = v_l_1436_;
goto _start;
}
case 1:
{
lean_inc(v_v_1435_);
return v_v_1435_;
}
default: 
{
v_t_1431_ = v_r_1437_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1433_);
return v_fallback_1433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1441_, lean_object* v_k_1442_, lean_object* v_fallback_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1441_, v_k_1442_, v_fallback_1443_);
lean_dec(v_fallback_1443_);
lean_dec(v_k_1442_);
lean_dec(v_t_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1453_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1454_ = lean_st_ref_get(v___x_1453_);
v___x_1455_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1456_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1454_, v_aliasName_1451_, v___x_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1458_);
lean_dec(v_aliasName_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1461_, lean_object* v_t_1462_, lean_object* v_k_1463_, lean_object* v_fallback_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1462_, v_k_1463_, v_fallback_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1466_, lean_object* v_t_1467_, lean_object* v_k_1468_, lean_object* v_fallback_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1466_, v_t_1467_, v_k_1468_, v_fallback_1469_);
lean_dec(v_fallback_1469_);
lean_dec(v_k_1468_);
lean_dec(v_t_1467_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1471_, lean_object* v_declName_1472_, lean_object* v_p_1473_, lean_object* v_kind_x3f_1474_, lean_object* v_info_1475_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1471_);
v___x_1494_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1493_, v_aliasName_1471_, v_p_1473_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_dec_ref_known(v___x_1494_, 1);
if (lean_obj_tag(v_kind_x3f_1474_) == 1)
{
lean_object* v_val_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_val_1495_ = lean_ctor_get(v_kind_x3f_1474_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v_kind_x3f_1474_, 1);
v___x_1496_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1497_ = lean_st_ref_take(v___x_1496_);
lean_inc(v_aliasName_1471_);
v___x_1498_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1471_, v_val_1495_, v___x_1497_);
v___x_1499_ = lean_st_ref_put(v___x_1496_, v___x_1498_);
goto v___jp_1477_;
}
else
{
lean_dec(v_kind_x3f_1474_);
goto v___jp_1477_;
}
}
else
{
lean_dec_ref(v_info_1475_);
lean_dec(v_kind_x3f_1474_);
lean_dec(v_declName_1472_);
lean_dec(v_aliasName_1471_);
return v___x_1494_;
}
v___jp_1477_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_stackSz_x3f_1480_; uint8_t v_autoGroupArgs_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1491_; 
v___x_1478_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1479_ = lean_st_ref_take(v___x_1478_);
v_stackSz_x3f_1480_ = lean_ctor_get(v_info_1475_, 1);
v_autoGroupArgs_1481_ = lean_ctor_get_uint8(v_info_1475_, sizeof(void*)*2);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_info_1475_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_info_1475_, 0);
lean_dec(v_unused_1492_);
v___x_1483_ = v_info_1475_;
v_isShared_1484_ = v_isSharedCheck_1491_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_stackSz_x3f_1480_);
lean_dec(v_info_1475_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1491_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v_declName_1472_);
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_declName_1472_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_stackSz_x3f_1480_);
lean_ctor_set_uint8(v_reuseFailAlloc_1490_, sizeof(void*)*2, v_autoGroupArgs_1481_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1471_, v___x_1486_, v___x_1479_);
v___x_1488_ = lean_st_ref_put(v___x_1478_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1500_, lean_object* v_declName_1501_, lean_object* v_p_1502_, lean_object* v_kind_x3f_1503_, lean_object* v_info_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Parser_registerAlias(v_aliasName_1500_, v_declName_1501_, v_p_1502_, v_kind_x3f_1503_, v_info_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_p_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_p_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_p_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1537_; 
v___x_1521_ = l_Lean_Parser_parserAliasesRef;
v___x_1522_ = l_Lean_Parser_getAlias___redArg(v___x_1521_, v_aliasName_1519_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1537_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1537_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
if (lean_obj_tag(v_a_1523_) == 1)
{
uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_dec_ref_known(v_a_1523_, 1);
v___x_1527_ = 1;
v___x_1528_ = lean_box(v___x_1527_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1528_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
else
{
uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
lean_dec(v_a_1523_);
v___x_1532_ = 0;
v___x_1533_ = lean_box(v___x_1532_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1533_);
v___x_1535_ = v___x_1525_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_Parser_isParserAlias(v_aliasName_1538_);
lean_dec(v_aliasName_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1543_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1544_ = lean_st_ref_get(v___x_1543_);
v___x_1545_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1544_, v_aliasName_1541_);
lean_dec(v___x_1544_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1547_);
lean_dec(v_aliasName_1547_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = l_Lean_Parser_parserAliasesRef;
v___x_1553_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1552_, v_aliasName_1550_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1553_, 0);
lean_dec(v_unused_1562_);
v___x_1555_ = v___x_1553_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v___x_1553_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(0);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
v_a_1563_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1553_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1553_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1574_){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = l_Lean_Parser_parserAliasesRef;
v___x_1577_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1576_, v_aliasName_1574_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1585_; 
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v___x_1577_, 0);
lean_dec(v_unused_1586_);
v___x_1579_ = v___x_1577_;
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v___x_1577_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_box(0);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1587_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1577_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1577_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = l_Lean_Parser_parserAliasesRef;
v___x_1601_ = l_Lean_Parser_getConstAlias___redArg(v___x_1600_, v_aliasName_1598_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1609_; 
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v___x_1601_, 0);
lean_dec(v_unused_1610_);
v___x_1603_ = v___x_1601_;
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v___x_1601_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_box(0);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1601_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1601_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1630_, lean_object* v_compileParserDescr_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_env_1643_; lean_object* v_opts_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; 
v_env_1643_ = lean_ctor_get(v_a_1632_, 0);
v_opts_1644_ = lean_ctor_get(v_a_1632_, 1);
v___x_1645_ = 0;
lean_inc(v_constName_1630_);
lean_inc_ref(v_env_1643_);
v___x_1646_ = l_Lean_Environment_find_x3f(v_env_1643_, v_constName_1630_, v___x_1645_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v_compileParserDescr_1631_);
v___x_1647_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1648_ = 1;
v___x_1649_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1630_, v___x_1648_);
v___x_1650_ = lean_string_append(v___x_1647_, v___x_1649_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1652_ = lean_string_append(v___x_1650_, v___x_1651_);
v___x_1653_ = lean_mk_io_user_error(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
else
{
lean_object* v_val_1655_; lean_object* v___x_1656_; 
v_val_1655_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1656_ = l_Lean_ConstantInfo_type(v_val_1655_);
lean_dec(v_val_1655_);
if (lean_obj_tag(v___x_1656_) == 4)
{
lean_object* v_declName_1657_; 
v_declName_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_declName_1657_);
lean_dec_ref_known(v___x_1656_, 2);
if (lean_obj_tag(v_declName_1657_) == 1)
{
lean_object* v_pre_1658_; 
v_pre_1658_ = lean_ctor_get(v_declName_1657_, 0);
lean_inc(v_pre_1658_);
if (lean_obj_tag(v_pre_1658_) == 1)
{
lean_object* v_pre_1659_; 
v_pre_1659_ = lean_ctor_get(v_pre_1658_, 0);
switch(lean_obj_tag(v_pre_1659_))
{
case 1:
{
lean_object* v_pre_1660_; 
lean_inc_ref(v_pre_1659_);
lean_dec_ref(v_compileParserDescr_1631_);
v_pre_1660_ = lean_ctor_get(v_pre_1659_, 0);
if (lean_obj_tag(v_pre_1660_) == 0)
{
lean_object* v_str_1661_; lean_object* v_str_1662_; lean_object* v_str_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_str_1661_ = lean_ctor_get(v_declName_1657_, 1);
lean_inc_ref(v_str_1661_);
lean_dec_ref_known(v_declName_1657_, 2);
v_str_1662_ = lean_ctor_get(v_pre_1658_, 1);
lean_inc_ref(v_str_1662_);
lean_dec_ref_known(v_pre_1658_, 2);
v_str_1663_ = lean_ctor_get(v_pre_1659_, 1);
lean_inc_ref(v_str_1663_);
lean_dec_ref_known(v_pre_1659_, 2);
v___x_1664_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1665_ = lean_string_dec_eq(v_str_1663_, v___x_1664_);
lean_dec_ref(v_str_1663_);
if (v___x_1665_ == 0)
{
lean_dec_ref(v_str_1662_);
lean_dec_ref(v_str_1661_);
goto v___jp_1634_;
}
else
{
lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1667_ = lean_string_dec_eq(v_str_1662_, v___x_1666_);
lean_dec_ref(v_str_1662_);
if (v___x_1667_ == 0)
{
lean_dec_ref(v_str_1661_);
goto v___jp_1634_;
}
else
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1669_ = lean_string_dec_eq(v_str_1661_, v___x_1668_);
if (v___x_1669_ == 0)
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_string_dec_eq(v_str_1661_, v___x_1666_);
lean_dec_ref(v_str_1661_);
if (v___x_1670_ == 0)
{
goto v___jp_1634_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = l_Lean_Environment_evalConst___redArg(v_env_1643_, v_opts_1644_, v_constName_1630_, v___x_1670_);
lean_dec(v_constName_1630_);
v___x_1672_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1671_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1677_ = lean_box(v___x_1670_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_a_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1672_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1672_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec_ref(v_str_1661_);
v___x_1691_ = l_Lean_Environment_evalConst___redArg(v_env_1643_, v_opts_1644_, v_constName_1630_, v___x_1669_);
lean_dec(v_constName_1630_);
v___x_1692_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1691_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1702_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1697_ = lean_box(v___x_1645_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v_a_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1698_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_a_1703_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1692_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1692_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1659_, 2);
lean_dec_ref_known(v_pre_1658_, 2);
lean_dec_ref_known(v_declName_1657_, 2);
goto v___jp_1634_;
}
}
case 0:
{
lean_object* v_str_1711_; lean_object* v_str_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v_str_1711_ = lean_ctor_get(v_declName_1657_, 1);
lean_inc_ref(v_str_1711_);
lean_dec_ref_known(v_declName_1657_, 2);
v_str_1712_ = lean_ctor_get(v_pre_1658_, 1);
lean_inc_ref(v_str_1712_);
lean_dec_ref_known(v_pre_1658_, 2);
v___x_1713_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1714_ = lean_string_dec_eq(v_str_1712_, v___x_1713_);
lean_dec_ref(v_str_1712_);
if (v___x_1714_ == 0)
{
lean_dec_ref(v_str_1711_);
lean_dec_ref(v_compileParserDescr_1631_);
goto v___jp_1634_;
}
else
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1716_ = lean_string_dec_eq(v_str_1711_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1717_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1718_ = lean_string_dec_eq(v_str_1711_, v___x_1717_);
lean_dec_ref(v_str_1711_);
if (v___x_1718_ == 0)
{
lean_dec_ref(v_compileParserDescr_1631_);
goto v___jp_1634_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = l_Lean_Environment_evalConst___redArg(v_env_1643_, v_opts_1644_, v_constName_1630_, v___x_1718_);
lean_dec(v_constName_1630_);
v___x_1720_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
lean_inc_ref(v_a_1632_);
v___x_1722_ = lean_apply_3(v_compileParserDescr_1631_, v_a_1721_, v_a_1632_, lean_box(0));
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1732_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1727_ = lean_box(v___x_1645_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
lean_ctor_set(v___x_1728_, 1, v_a_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1728_);
v___x_1730_ = v___x_1725_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_a_1733_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1722_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1722_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v_compileParserDescr_1631_);
v_a_1741_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1720_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1720_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec_ref(v_str_1711_);
v___x_1749_ = l_Lean_Environment_evalConst___redArg(v_env_1643_, v_opts_1644_, v_constName_1630_, v___x_1716_);
lean_dec(v_constName_1630_);
v___x_1750_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1749_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
lean_inc_ref(v_a_1632_);
v___x_1752_ = lean_apply_3(v_compileParserDescr_1631_, v_a_1751_, v_a_1632_, lean_box(0));
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1762_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1762_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1762_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1757_ = lean_box(v___x_1716_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v_a_1753_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1758_);
v___x_1760_ = v___x_1755_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1752_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1752_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v_compileParserDescr_1631_);
v_a_1771_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1750_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1750_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_pre_1658_, 2);
lean_dec_ref_known(v_declName_1657_, 2);
lean_dec_ref(v_compileParserDescr_1631_);
goto v___jp_1634_;
}
}
}
else
{
lean_dec(v_pre_1658_);
lean_dec_ref_known(v_declName_1657_, 2);
lean_dec_ref(v_compileParserDescr_1631_);
goto v___jp_1634_;
}
}
else
{
lean_dec(v_declName_1657_);
lean_dec_ref(v_compileParserDescr_1631_);
goto v___jp_1634_;
}
}
else
{
lean_dec_ref(v___x_1656_);
lean_dec_ref(v_compileParserDescr_1631_);
goto v___jp_1634_;
}
}
v___jp_1634_:
{
lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1635_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1636_ = 1;
v___x_1637_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1630_, v___x_1636_);
v___x_1638_ = lean_string_append(v___x_1635_, v___x_1637_);
lean_dec_ref(v___x_1637_);
v___x_1639_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1640_ = lean_string_append(v___x_1638_, v___x_1639_);
v___x_1641_ = lean_mk_io_user_error(v___x_1640_);
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1779_, lean_object* v_compileParserDescr_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1779_, v_compileParserDescr_1780_, v_a_1781_);
lean_dec_ref(v_a_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1784_, v_a_1785_, v_a_1786_);
lean_dec_ref(v_a_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
switch(lean_obj_tag(v_a_1790_))
{
case 0:
{
lean_object* v_name_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v_categories_1789_);
v_name_1793_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_name_1793_);
lean_dec_ref_known(v_a_1790_, 1);
v___x_1794_ = l_Lean_Parser_parserAliasesRef;
v___x_1795_ = l_Lean_Parser_getConstAlias___redArg(v___x_1794_, v_name_1793_);
return v___x_1795_;
}
case 1:
{
lean_object* v_name_1796_; lean_object* v_p_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_name_1796_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_name_1796_);
v_p_1797_ = lean_ctor_get(v_a_1790_, 1);
lean_inc_ref(v_p_1797_);
lean_dec_ref_known(v_a_1790_, 2);
v___x_1798_ = l_Lean_Parser_parserAliasesRef;
v___x_1799_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1798_, v_name_1796_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_p_1797_, v_a_1791_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1810_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = lean_apply_1(v_a_1800_, v_a_1802_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1806_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
else
{
lean_dec(v_a_1800_);
return v___x_1801_;
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_p_1797_);
lean_dec_ref(v_categories_1789_);
v_a_1811_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1799_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1799_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
case 2:
{
lean_object* v_name_1819_; lean_object* v_p_u2081_1820_; lean_object* v_p_u2082_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_name_1819_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_name_1819_);
v_p_u2081_1820_ = lean_ctor_get(v_a_1790_, 1);
lean_inc_ref(v_p_u2081_1820_);
v_p_u2082_1821_ = lean_ctor_get(v_a_1790_, 2);
lean_inc_ref(v_p_u2082_1821_);
lean_dec_ref_known(v_a_1790_, 3);
v___x_1822_ = l_Lean_Parser_parserAliasesRef;
v___x_1823_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1822_, v_name_1819_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
lean_inc_ref(v_categories_1789_);
v___x_1825_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_p_u2081_1820_, v_a_1791_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_p_u2082_1821_, v_a_1791_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1836_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_apply_2(v_a_1824_, v_a_1826_, v_a_1828_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1832_);
v___x_1834_ = v___x_1830_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_dec(v_a_1826_);
lean_dec(v_a_1824_);
return v___x_1827_;
}
}
else
{
lean_dec(v_a_1824_);
lean_dec_ref(v_p_u2082_1821_);
lean_dec_ref(v_categories_1789_);
return v___x_1825_;
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v_p_u2082_1821_);
lean_dec_ref(v_p_u2081_1820_);
lean_dec_ref(v_categories_1789_);
v_a_1837_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1823_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1823_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
case 3:
{
lean_object* v_kind_1845_; lean_object* v_prec_1846_; lean_object* v_p_1847_; lean_object* v___x_1848_; 
v_kind_1845_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_kind_1845_);
v_prec_1846_ = lean_ctor_get(v_a_1790_, 1);
lean_inc(v_prec_1846_);
v_p_1847_ = lean_ctor_get(v_a_1790_, 2);
lean_inc_ref(v_p_1847_);
lean_dec_ref_known(v_a_1790_, 3);
v___x_1848_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_p_1847_, v_a_1791_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = l_Lean_Parser_leadingNode(v_kind_1845_, v_prec_1846_, v_a_1849_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_dec(v_prec_1846_);
lean_dec(v_kind_1845_);
return v___x_1848_;
}
}
case 4:
{
lean_object* v_kind_1858_; lean_object* v_prec_1859_; lean_object* v_lhsPrec_1860_; lean_object* v_p_1861_; lean_object* v___x_1862_; 
v_kind_1858_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_kind_1858_);
v_prec_1859_ = lean_ctor_get(v_a_1790_, 1);
lean_inc(v_prec_1859_);
v_lhsPrec_1860_ = lean_ctor_get(v_a_1790_, 2);
lean_inc(v_lhsPrec_1860_);
v_p_1861_ = lean_ctor_get(v_a_1790_, 3);
lean_inc_ref(v_p_1861_);
lean_dec_ref_known(v_a_1790_, 4);
v___x_1862_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_p_1861_, v_a_1791_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = l_Lean_Parser_trailingNode(v_kind_1858_, v_prec_1859_, v_lhsPrec_1860_, v_a_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_dec(v_lhsPrec_1860_);
lean_dec(v_prec_1859_);
lean_dec(v_kind_1858_);
return v___x_1862_;
}
}
case 5:
{
lean_object* v_val_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v_categories_1789_);
v_val_1872_ = lean_ctor_get(v_a_1790_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_a_1790_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1874_ = v_a_1790_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_val_1872_);
lean_dec(v_a_1790_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = l_Lean_Parser_symbol(v_val_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
case 6:
{
lean_object* v_val_1881_; uint8_t v_includeIdent_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec_ref(v_categories_1789_);
v_val_1881_ = lean_ctor_get(v_a_1790_, 0);
lean_inc_ref(v_val_1881_);
v_includeIdent_1882_ = lean_ctor_get_uint8(v_a_1790_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1790_, 1);
v___x_1883_ = l_Lean_Parser_nonReservedSymbol(v_val_1881_, v_includeIdent_1882_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
case 7:
{
lean_object* v_catName_1885_; lean_object* v_rbp_1886_; lean_object* v___x_1887_; 
v_catName_1885_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_catName_1885_);
v_rbp_1886_ = lean_ctor_get(v_a_1790_, 1);
lean_inc(v_rbp_1886_);
lean_dec_ref_known(v_a_1790_, 2);
v___x_1887_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1789_, v_catName_1885_);
lean_dec_ref(v_categories_1789_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec(v_rbp_1886_);
v___x_1888_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1885_);
v___x_1889_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1888_);
return v___x_1889_;
}
else
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v___x_1887_, 0);
lean_dec(v_unused_1898_);
v___x_1891_ = v___x_1887_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v___x_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = l_Lean_Parser_categoryParser(v_catName_1885_, v_rbp_1886_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
case 8:
{
lean_object* v_declName_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_declName_1899_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_declName_1899_);
lean_dec_ref_known(v_a_1790_, 1);
v___x_1900_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1900_, 0, v_categories_1789_);
v___x_1901_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1899_, v___x_1900_, v_a_1791_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1910_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v_snd_1906_; lean_object* v___x_1908_; 
v_snd_1906_ = lean_ctor_get(v_a_1902_, 1);
lean_inc(v_snd_1906_);
lean_dec(v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_snd_1906_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_snd_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_a_1911_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1901_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1901_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
case 9:
{
lean_object* v_name_1919_; lean_object* v_kind_1920_; lean_object* v_p_1921_; lean_object* v___x_1922_; 
v_name_1919_ = lean_ctor_get(v_a_1790_, 0);
lean_inc_ref(v_name_1919_);
v_kind_1920_ = lean_ctor_get(v_a_1790_, 1);
lean_inc(v_kind_1920_);
v_p_1921_ = lean_ctor_get(v_a_1790_, 2);
lean_inc_ref(v_p_1921_);
lean_dec_ref_known(v_a_1790_, 3);
v___x_1922_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_p_1921_, v_a_1791_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1933_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1927_ = 1;
lean_inc(v_kind_1920_);
v___x_1928_ = l_Lean_Parser_nodeWithAntiquot(v_name_1919_, v_kind_1920_, v_a_1923_, v___x_1927_);
v___x_1929_ = l_Lean_Parser_withCache(v_kind_1920_, v___x_1928_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1929_);
v___x_1931_ = v___x_1925_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_dec(v_kind_1920_);
lean_dec_ref(v_name_1919_);
return v___x_1922_;
}
}
case 10:
{
lean_object* v_p_1934_; lean_object* v_sep_1935_; lean_object* v_psep_1936_; uint8_t v_allowTrailingSep_1937_; lean_object* v___x_1938_; 
v_p_1934_ = lean_ctor_get(v_a_1790_, 0);
lean_inc_ref(v_p_1934_);
v_sep_1935_ = lean_ctor_get(v_a_1790_, 1);
lean_inc_ref(v_sep_1935_);
v_psep_1936_ = lean_ctor_get(v_a_1790_, 2);
lean_inc_ref(v_psep_1936_);
v_allowTrailingSep_1937_ = lean_ctor_get_uint8(v_a_1790_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1790_, 3);
lean_inc_ref(v_categories_1789_);
v___x_1938_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_p_1934_, v_a_1791_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1940_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_psep_1936_, v_a_1791_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1949_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = l_Lean_Parser_sepBy(v_a_1939_, v_sep_1935_, v_a_1941_, v_allowTrailingSep_1937_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
else
{
lean_dec(v_a_1939_);
lean_dec_ref(v_sep_1935_);
return v___x_1940_;
}
}
else
{
lean_dec_ref(v_psep_1936_);
lean_dec_ref(v_sep_1935_);
lean_dec_ref(v_categories_1789_);
return v___x_1938_;
}
}
case 11:
{
lean_object* v_p_1950_; lean_object* v_sep_1951_; lean_object* v_psep_1952_; uint8_t v_allowTrailingSep_1953_; lean_object* v___x_1954_; 
v_p_1950_ = lean_ctor_get(v_a_1790_, 0);
lean_inc_ref(v_p_1950_);
v_sep_1951_ = lean_ctor_get(v_a_1790_, 1);
lean_inc_ref(v_sep_1951_);
v_psep_1952_ = lean_ctor_get(v_a_1790_, 2);
lean_inc_ref(v_psep_1952_);
v_allowTrailingSep_1953_ = lean_ctor_get_uint8(v_a_1790_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1790_, 3);
lean_inc_ref(v_categories_1789_);
v___x_1954_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_p_1950_, v_a_1791_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1956_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_psep_1952_, v_a_1791_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = l_Lean_Parser_sepBy1(v_a_1955_, v_sep_1951_, v_a_1957_, v_allowTrailingSep_1953_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
lean_dec(v_a_1955_);
lean_dec_ref(v_sep_1951_);
return v___x_1956_;
}
}
else
{
lean_dec_ref(v_psep_1952_);
lean_dec_ref(v_sep_1951_);
lean_dec_ref(v_categories_1789_);
return v___x_1954_;
}
}
default: 
{
lean_object* v_val_1966_; lean_object* v_asciiVal_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec_ref(v_categories_1789_);
v_val_1966_ = lean_ctor_get(v_a_1790_, 0);
lean_inc_ref(v_val_1966_);
v_asciiVal_1967_ = lean_ctor_get(v_a_1790_, 1);
lean_inc_ref(v_asciiVal_1967_);
lean_dec_ref_known(v_a_1790_, 2);
v___x_1968_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1966_, v_asciiVal_1967_);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_1970_, lean_object* v_d_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1970_, v_d_1971_, v_a_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_1975_, lean_object* v_d_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Parser_compileParserDescr(v_categories_1975_, v_d_1976_, v_a_1977_);
lean_dec_ref(v_a_1977_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1980_, v___y_1981_, v___y_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_1985_, v___y_1986_, v___y_1987_);
lean_dec_ref(v___y_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_1990_, lean_object* v_constName_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___f_1994_; lean_object* v___x_1995_; 
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1994_, 0, v_categories_1990_);
v___x_1995_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1991_, v___f_1994_, v_a_1992_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_1996_, lean_object* v_constName_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Parser_mkParserOfConstant(v_categories_1996_, v_constName_1997_, v_a_1998_);
lean_dec_ref(v_a_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_st_mk_ref(v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2009_ = l_Lean_Parser_parserAttributeHooks;
v___x_2010_ = lean_st_ref_take(v___x_2009_);
v___x_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2011_, 0, v_hook_2007_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_st_ref_put(v___x_2009_, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2017_, lean_object* v_declName_2018_, uint8_t v_builtin_2019_, lean_object* v_as_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
if (lean_obj_tag(v_as_2020_) == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec(v_declName_2018_);
lean_dec(v_catName_2017_);
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
else
{
lean_object* v_head_2026_; lean_object* v_tail_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_head_2026_ = lean_ctor_get(v_as_2020_, 0);
lean_inc(v_head_2026_);
v_tail_2027_ = lean_ctor_get(v_as_2020_, 1);
lean_inc(v_tail_2027_);
lean_dec_ref_known(v_as_2020_, 2);
v___x_2028_ = lean_box(v_builtin_2019_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc(v_declName_2018_);
lean_inc(v_catName_2017_);
v___x_2029_ = lean_apply_6(v_head_2026_, v_catName_2017_, v_declName_2018_, v___x_2028_, v___y_2021_, v___y_2022_, lean_box(0));
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec_ref_known(v___x_2029_, 1);
v_as_2020_ = v_tail_2027_;
goto _start;
}
else
{
lean_dec(v_tail_2027_);
lean_dec(v_declName_2018_);
lean_dec(v_catName_2017_);
return v___x_2029_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2031_, lean_object* v_declName_2032_, lean_object* v_builtin_2033_, lean_object* v_as_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
uint8_t v_builtin_boxed_2038_; lean_object* v_res_2039_; 
v_builtin_boxed_2038_ = lean_unbox(v_builtin_2033_);
v_res_2039_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2031_, v_declName_2032_, v_builtin_boxed_2038_, v_as_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2040_, lean_object* v_declName_2041_, uint8_t v_builtin_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = l_Lean_Parser_parserAttributeHooks;
v___x_2047_ = lean_st_ref_get(v___x_2046_);
v___x_2048_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2040_, v_declName_2041_, v_builtin_2042_, v___x_2047_, v_a_2043_, v_a_2044_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2049_, lean_object* v_declName_2050_, lean_object* v_builtin_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
uint8_t v_builtin_boxed_2055_; lean_object* v_res_2056_; 
v_builtin_boxed_2055_ = lean_unbox(v_builtin_2051_);
v_res_2056_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2049_, v_declName_2050_, v_builtin_boxed_2055_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2057_, lean_object* v_decl_2058_, lean_object* v_stx_2059_, uint8_t v_x_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2059_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2064_) == 0)
{
uint8_t v___x_2065_; lean_object* v___x_2066_; 
lean_dec_ref_known(v___x_2064_, 1);
v___x_2065_ = 1;
v___x_2066_ = l_Lean_Parser_runParserAttributeHooks(v___x_2057_, v_decl_2058_, v___x_2065_, v___y_2061_, v___y_2062_);
return v___x_2066_;
}
else
{
lean_dec(v_decl_2058_);
lean_dec(v___x_2057_);
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2067_, lean_object* v_decl_2068_, lean_object* v_stx_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
uint8_t v_x_1082__boxed_2074_; lean_object* v_res_2075_; 
v_x_1082__boxed_2074_ = lean_unbox(v_x_2070_);
v_res_2075_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2067_, v_decl_2068_, v_stx_2069_, v_x_1082__boxed_2074_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2075_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
lean_ctor_set(v___x_2081_, 2, v___x_2080_);
lean_ctor_set(v___x_2081_, 3, v___x_2080_);
lean_ctor_set(v___x_2081_, 4, v___x_2079_);
lean_ctor_set(v___x_2081_, 5, v___x_2079_);
lean_ctor_set(v___x_2081_, 6, v___x_2079_);
lean_ctor_set(v___x_2081_, 7, v___x_2079_);
lean_ctor_set(v___x_2081_, 8, v___x_2079_);
lean_ctor_set(v___x_2081_, 9, v___x_2079_);
lean_ctor_set(v___x_2081_, 10, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = lean_unsigned_to_nat(32u);
v___x_2083_ = lean_mk_empty_array_with_capacity(v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2085_ = ((size_t)5ULL);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_unsigned_to_nat(32u);
v___x_2088_ = lean_mk_empty_array_with_capacity(v___x_2087_);
v___x_2089_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2090_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2088_);
lean_ctor_set(v___x_2090_, 2, v___x_2086_);
lean_ctor_set(v___x_2090_, 3, v___x_2086_);
lean_ctor_set_usize(v___x_2090_, 4, v___x_2085_);
return v___x_2090_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2091_ = lean_box(1);
v___x_2092_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2093_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___x_2092_);
lean_ctor_set(v___x_2094_, 2, v___x_2091_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v_env_2100_; lean_object* v_options_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2099_ = lean_st_ref_get(v___y_2097_);
v_env_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_env_2100_);
lean_dec(v___x_2099_);
v_options_2101_ = lean_ctor_get(v___y_2096_, 2);
v___x_2102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2101_);
v___x_2104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2104_, 0, v_env_2100_);
lean_ctor_set(v___x_2104_, 1, v___x_2102_);
lean_ctor_set(v___x_2104_, 2, v___x_2103_);
lean_ctor_set(v___x_2104_, 3, v_options_2101_);
v___x_2105_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v_msgData_2095_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_ref_2116_; lean_object* v___x_2117_; lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2126_; 
v_ref_2116_ = lean_ctor_get(v___y_2113_, 5);
v___x_2117_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2112_, v___y_2113_, v___y_2114_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
lean_inc(v_ref_2116_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v_ref_2116_);
lean_ctor_set(v___x_2122_, 1, v_a_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 1);
lean_ctor_set(v___x_2120_, 0, v___x_2122_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2131_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2137_ = l_Lean_stringToMessageData(v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2138_, lean_object* v_decl_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2143_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2144_ = l_Lean_MessageData_ofName(v___x_2138_);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2147_, v___y_2140_, v___y_2141_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2149_, lean_object* v_decl_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2149_, v_decl_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v_decl_2150_);
return v_res_2154_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_unsigned_to_nat(3646333153u);
v___x_2198_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2199_ = l_Lean_Name_num___override(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2202_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2203_ = l_Lean_Name_str___override(v___x_2202_, v___x_2201_);
return v___x_2203_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2206_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2207_ = l_Lean_Name_str___override(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_unsigned_to_nat(2u);
v___x_2209_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2210_ = l_Lean_Name_num___override(v___x_2209_, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2217_ = 0;
v___x_2218_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2219_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2220_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2221_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2219_);
lean_ctor_set(v___x_2221_, 2, v___x_2218_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*3, v___x_2217_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2222_; lean_object* v___f_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___f_2222_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2223_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2224_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v___f_2223_);
lean_ctor_set(v___x_2225_, 2, v___f_2222_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2228_ = l_Lean_registerBuiltinAttribute(v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2231_, lean_object* v_msg_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2232_, v___y_2233_, v___y_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2237_, lean_object* v_msg_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2237_, v_msg_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2243_, lean_object* v_decl_2244_, lean_object* v_stx_2245_, uint8_t v_x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2245_, v___y_2247_, v___y_2248_);
if (lean_obj_tag(v___x_2250_) == 0)
{
uint8_t v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref_known(v___x_2250_, 1);
v___x_2251_ = 0;
v___x_2252_ = l_Lean_Parser_runParserAttributeHooks(v___x_2243_, v_decl_2244_, v___x_2251_, v___y_2247_, v___y_2248_);
return v___x_2252_;
}
else
{
lean_dec(v_decl_2244_);
lean_dec(v___x_2243_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2253_, lean_object* v_decl_2254_, lean_object* v_stx_2255_, lean_object* v_x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v_x_211__boxed_2260_; lean_object* v_res_2261_; 
v_x_211__boxed_2260_ = lean_unbox(v_x_2256_);
v_res_2261_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2253_, v_decl_2254_, v_stx_2255_, v_x_211__boxed_2260_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2262_, lean_object* v_decl_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2267_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2268_ = l_Lean_MessageData_ofName(v___x_2262_);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2271_, v___y_2264_, v___y_2265_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2273_, lean_object* v_decl_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2273_, v_decl_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_decl_2274_);
return v_res_2278_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_unsigned_to_nat(3789407938u);
v___x_2282_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2283_ = l_Lean_Name_num___override(v___x_2282_, v___x_2281_);
return v___x_2283_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2285_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2286_ = l_Lean_Name_str___override(v___x_2285_, v___x_2284_);
return v___x_2286_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2288_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2289_ = l_Lean_Name_str___override(v___x_2288_, v___x_2287_);
return v___x_2289_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_unsigned_to_nat(2u);
v___x_2291_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2292_ = l_Lean_Name_num___override(v___x_2291_, v___x_2290_);
return v___x_2292_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2299_ = 0;
v___x_2300_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2301_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2302_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2303_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v___x_2301_);
lean_ctor_set(v___x_2303_, 2, v___x_2300_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*3, v___x_2299_);
return v___x_2303_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___f_2304_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2305_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2306_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___f_2305_);
lean_ctor_set(v___x_2307_, 2, v___f_2304_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2310_ = l_Lean_registerBuiltinAttribute(v___x_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2313_, lean_object* v_x_2314_, lean_object* v_a_2315_){
_start:
{
switch(lean_obj_tag(v_x_2314_))
{
case 0:
{
lean_object* v_val_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_s_2313_);
v_val_2317_ = lean_ctor_get(v_x_2314_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_x_2314_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2319_ = v_x_2314_;
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_val_2317_);
lean_dec(v_x_2314_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_val_2317_);
v___x_2322_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
case 1:
{
lean_object* v_val_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v_s_2313_);
v_val_2326_ = lean_ctor_get(v_x_2314_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_x_2314_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v_x_2314_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_val_2326_);
lean_dec(v_x_2314_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_val_2326_);
v___x_2331_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
}
}
case 2:
{
lean_object* v_catName_2335_; lean_object* v_declName_2336_; uint8_t v_behavior_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v_s_2313_);
v_catName_2335_ = lean_ctor_get(v_x_2314_, 0);
v_declName_2336_ = lean_ctor_get(v_x_2314_, 1);
v_behavior_2337_ = lean_ctor_get_uint8(v_x_2314_, sizeof(void*)*2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_x_2314_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2339_ = v_x_2314_;
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_declName_2336_);
lean_inc(v_catName_2335_);
lean_dec(v_x_2314_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2345_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_catName_2335_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_declName_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, sizeof(void*)*2, v_behavior_2337_);
v___x_2342_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
}
default: 
{
lean_object* v_catName_2346_; lean_object* v_declName_2347_; lean_object* v_prio_2348_; lean_object* v_categories_2349_; lean_object* v___x_2350_; 
v_catName_2346_ = lean_ctor_get(v_x_2314_, 0);
lean_inc(v_catName_2346_);
v_declName_2347_ = lean_ctor_get(v_x_2314_, 1);
lean_inc_n(v_declName_2347_, 2);
v_prio_2348_ = lean_ctor_get(v_x_2314_, 2);
lean_inc(v_prio_2348_);
lean_dec_ref_known(v_x_2314_, 3);
v_categories_2349_ = lean_ctor_get(v_s_2313_, 2);
lean_inc_ref(v_categories_2349_);
lean_dec_ref(v_s_2313_);
v___x_2350_ = l_Lean_Parser_mkParserOfConstant(v_categories_2349_, v_declName_2347_, v_a_2315_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2362_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2362_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2362_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_fst_2355_; lean_object* v_snd_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2360_; 
v_fst_2355_ = lean_ctor_get(v_a_2351_, 0);
lean_inc(v_fst_2355_);
v_snd_2356_ = lean_ctor_get(v_a_2351_, 1);
lean_inc(v_snd_2356_);
lean_dec(v_a_2351_);
v___x_2357_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2357_, 0, v_catName_2346_);
lean_ctor_set(v___x_2357_, 1, v_declName_2347_);
lean_ctor_set(v___x_2357_, 2, v_snd_2356_);
lean_ctor_set(v___x_2357_, 3, v_prio_2348_);
v___x_2358_ = lean_unbox(v_fst_2355_);
lean_dec(v_fst_2355_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*4, v___x_2358_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2357_);
v___x_2360_ = v___x_2353_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2357_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_prio_2348_);
lean_dec(v_declName_2347_);
lean_dec(v_catName_2346_);
v_a_2363_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2350_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2350_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2371_, lean_object* v_x_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2371_, v_x_2372_, v_a_2373_);
lean_dec_ref(v_a_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_a_2377_);
lean_inc_ref_n(v___x_2378_, 2);
v___x_2379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
lean_ctor_set(v___x_2379_, 2, v___x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2380_, v_a_2381_);
lean_dec_ref(v_x_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2383_){
_start:
{
lean_inc_ref(v___y_2383_);
return v___y_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2384_);
lean_dec_ref(v___y_2384_);
return v_res_2385_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2396_; lean_object* v___f_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___f_2396_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2397_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2398_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2399_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2400_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2401_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2402_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2403_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v___x_2401_);
lean_ctor_set(v___x_2403_, 2, v___x_2400_);
lean_ctor_set(v___x_2403_, 3, v___x_2399_);
lean_ctor_set(v___x_2403_, 4, v___x_2398_);
lean_ctor_set(v___x_2403_, 5, v___f_2397_);
lean_ctor_set(v___x_2403_, 6, v___f_2396_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2406_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2409_, lean_object* v_catName_2410_){
_start:
{
lean_object* v___x_2411_; lean_object* v_ext_2412_; lean_object* v_toEnvExtension_2413_; lean_object* v_asyncMode_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_categories_2417_; lean_object* v___x_2418_; 
v___x_2411_ = l_Lean_Parser_parserExtension;
v_ext_2412_ = lean_ctor_get(v___x_2411_, 1);
v_toEnvExtension_2413_ = lean_ctor_get(v_ext_2412_, 0);
v_asyncMode_2414_ = lean_ctor_get(v_toEnvExtension_2413_, 2);
v___x_2415_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2416_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2415_, v___x_2411_, v_env_2409_, v_asyncMode_2414_);
v_categories_2417_ = lean_ctor_get(v___x_2416_, 2);
lean_inc_ref(v_categories_2417_);
lean_dec(v___x_2416_);
v___x_2418_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2417_, v_catName_2410_);
lean_dec_ref(v_categories_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2419_, lean_object* v_catName_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_Parser_getParserCategory_x3f(v_env_2419_, v_catName_2420_);
lean_dec(v_catName_2420_);
return v_res_2421_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2422_, lean_object* v_catName_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_Parser_getParserCategory_x3f(v_env_2422_, v_catName_2423_);
if (lean_obj_tag(v___x_2424_) == 0)
{
uint8_t v___x_2425_; 
v___x_2425_ = 0;
return v___x_2425_;
}
else
{
uint8_t v___x_2426_; 
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = 1;
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2427_, lean_object* v_catName_2428_){
_start:
{
uint8_t v_res_2429_; lean_object* v_r_2430_; 
v_res_2429_ = l_Lean_Parser_isParserCategory(v_env_2427_, v_catName_2428_);
lean_dec(v_catName_2428_);
v_r_2430_ = lean_box(v_res_2429_);
return v_r_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2431_, lean_object* v_catName_2432_, lean_object* v_declName_2433_, uint8_t v_behavior_2434_){
_start:
{
uint8_t v___x_2435_; 
lean_inc_ref(v_env_2431_);
v___x_2435_ = l_Lean_Parser_isParserCategory(v_env_2431_, v_catName_2432_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2436_ = l_Lean_Parser_parserExtension;
v___x_2437_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2437_, 0, v_catName_2432_);
lean_ctor_set(v___x_2437_, 1, v_declName_2433_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*2, v_behavior_2434_);
v___x_2438_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2436_, v_env_2431_, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
else
{
lean_object* v___x_2440_; 
lean_dec(v_declName_2433_);
lean_dec_ref(v_env_2431_);
v___x_2440_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2432_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2441_, lean_object* v_catName_2442_, lean_object* v_declName_2443_, lean_object* v_behavior_2444_){
_start:
{
uint8_t v_behavior_boxed_2445_; lean_object* v_res_2446_; 
v_behavior_boxed_2445_ = lean_unbox(v_behavior_2444_);
v_res_2446_ = l_Lean_Parser_addParserCategory(v_env_2441_, v_catName_2442_, v_declName_2443_, v_behavior_boxed_2445_);
return v_res_2446_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2447_, lean_object* v_catName_2448_){
_start:
{
lean_object* v___x_2449_; lean_object* v_ext_2450_; lean_object* v_toEnvExtension_2451_; lean_object* v_asyncMode_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v_categories_2455_; lean_object* v___x_2456_; 
v___x_2449_ = l_Lean_Parser_parserExtension;
v_ext_2450_ = lean_ctor_get(v___x_2449_, 1);
v_toEnvExtension_2451_ = lean_ctor_get(v_ext_2450_, 0);
v_asyncMode_2452_ = lean_ctor_get(v_toEnvExtension_2451_, 2);
v___x_2453_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2454_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2453_, v___x_2449_, v_env_2447_, v_asyncMode_2452_);
v_categories_2455_ = lean_ctor_get(v___x_2454_, 2);
lean_inc_ref(v_categories_2455_);
lean_dec(v___x_2454_);
v___x_2456_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2455_, v_catName_2448_);
lean_dec_ref(v_categories_2455_);
if (lean_obj_tag(v___x_2456_) == 0)
{
uint8_t v___x_2457_; 
v___x_2457_ = 0;
return v___x_2457_;
}
else
{
lean_object* v_val_2458_; uint8_t v_behavior_2459_; 
v_val_2458_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_val_2458_);
lean_dec_ref_known(v___x_2456_, 1);
v_behavior_2459_ = lean_ctor_get_uint8(v_val_2458_, sizeof(void*)*3);
lean_dec(v_val_2458_);
return v_behavior_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2460_, lean_object* v_catName_2461_){
_start:
{
uint8_t v_res_2462_; lean_object* v_r_2463_; 
v_res_2462_ = l_Lean_Parser_leadingIdentBehavior(v_env_2460_, v_catName_2461_);
lean_dec(v_catName_2461_);
v_r_2463_ = lean_box(v_res_2462_);
return v_r_2463_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2464_, lean_object* v_x_2465_){
_start:
{
if (lean_obj_tag(v_x_2465_) == 0)
{
return v_x_2464_;
}
else
{
lean_object* v_head_2466_; lean_object* v_tail_2467_; lean_object* v___x_2468_; 
v_head_2466_ = lean_ctor_get(v_x_2465_, 0);
lean_inc_n(v_head_2466_, 2);
v_tail_2467_ = lean_ctor_get(v_x_2465_, 1);
lean_inc(v_tail_2467_);
lean_dec_ref_known(v_x_2465_, 2);
v___x_2468_ = l_Lean_Data_Trie_insert___redArg(v_x_2464_, v_head_2466_, v_head_2466_);
lean_dec(v_head_2466_);
v_x_2464_ = v___x_2468_;
v_x_2465_ = v_tail_2467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2470_, lean_object* v_ctx_2471_){
_start:
{
lean_object* v_toInputContext_2472_; lean_object* v_toParserModuleContext_2473_; lean_object* v_toCacheableParserContext_2474_; lean_object* v_tokens_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2486_; 
v_toInputContext_2472_ = lean_ctor_get(v_ctx_2471_, 0);
v_toParserModuleContext_2473_ = lean_ctor_get(v_ctx_2471_, 1);
v_toCacheableParserContext_2474_ = lean_ctor_get(v_ctx_2471_, 2);
v_tokens_2475_ = lean_ctor_get(v_ctx_2471_, 3);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_ctx_2471_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2477_ = v_ctx_2471_;
v_isShared_2478_ = v_isSharedCheck_2486_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_tokens_2475_);
lean_inc(v_toCacheableParserContext_2474_);
lean_inc(v_toParserModuleContext_2473_);
lean_inc(v_toInputContext_2472_);
lean_dec(v_ctx_2471_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2486_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_collectTokens_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v_collectTokens_2479_ = lean_ctor_get(v_info_2470_, 0);
lean_inc_ref(v_collectTokens_2479_);
lean_dec_ref(v_info_2470_);
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_apply_1(v_collectTokens_2479_, v___x_2480_);
v___x_2482_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2475_, v___x_2481_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 3, v___x_2482_);
v___x_2484_ = v___x_2477_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_toInputContext_2472_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_toParserModuleContext_2473_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_toCacheableParserContext_2474_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2487_, lean_object* v_declName_2488_, lean_object* v___x_2489_, lean_object* v_ctx_2490_, lean_object* v_s_2491_, lean_object* v_evalFallback_x3f_2492_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_Parser_mkParserOfConstant(v_categories_2487_, v_declName_2488_, v___x_2489_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v_snd_2496_; lean_object* v_info_2497_; lean_object* v_fn_2498_; lean_object* v___f_2499_; lean_object* v___x_2500_; 
lean_dec(v_evalFallback_x3f_2492_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v_snd_2496_ = lean_ctor_get(v_a_2495_, 1);
lean_inc(v_snd_2496_);
lean_dec(v_a_2495_);
v_info_2497_ = lean_ctor_get(v_snd_2496_, 0);
lean_inc_ref(v_info_2497_);
v_fn_2498_ = lean_ctor_get(v_snd_2496_, 1);
lean_inc_ref(v_fn_2498_);
lean_dec(v_snd_2496_);
v___f_2499_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2499_, 0, v_info_2497_);
v___x_2500_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2499_, v_fn_2498_, v_ctx_2490_, v_s_2491_);
return v___x_2500_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2492_) == 1)
{
lean_object* v_val_2501_; lean_object* v___x_2502_; 
lean_dec_ref_known(v___x_2494_, 1);
v_val_2501_ = lean_ctor_get(v_evalFallback_x3f_2492_, 0);
lean_inc(v_val_2501_);
lean_dec_ref_known(v_evalFallback_x3f_2492_, 1);
v___x_2502_ = lean_apply_2(v_val_2501_, v_ctx_2490_, v_s_2491_);
return v___x_2502_;
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v_evalFallback_x3f_2492_);
lean_dec_ref(v_ctx_2490_);
v_a_2503_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2504_ = lean_io_error_to_string(v_a_2503_);
v___x_2505_ = lean_box(0);
v___x_2506_ = 1;
v___x_2507_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2491_, v___x_2504_, v___x_2505_, v___x_2506_);
return v___x_2507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2508_, lean_object* v_declName_2509_, lean_object* v___x_2510_, lean_object* v_ctx_2511_, lean_object* v_s_2512_, lean_object* v_evalFallback_x3f_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2508_, v_declName_2509_, v___x_2510_, v_ctx_2511_, v_s_2512_, v_evalFallback_x3f_2513_);
lean_dec_ref(v___x_2510_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2516_, lean_object* v_evalFallback_x3f_2517_, lean_object* v_ctx_2518_, lean_object* v_s_2519_){
_start:
{
lean_object* v_toParserModuleContext_2520_; lean_object* v_env_2521_; lean_object* v_options_2522_; lean_object* v___x_2523_; lean_object* v_ext_2524_; lean_object* v_toEnvExtension_2525_; lean_object* v_asyncMode_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_categories_2529_; lean_object* v___x_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; 
v_toParserModuleContext_2520_ = lean_ctor_get(v_ctx_2518_, 1);
v_env_2521_ = lean_ctor_get(v_toParserModuleContext_2520_, 0);
v_options_2522_ = lean_ctor_get(v_toParserModuleContext_2520_, 1);
v___x_2523_ = l_Lean_Parser_parserExtension;
v_ext_2524_ = lean_ctor_get(v___x_2523_, 1);
v_toEnvExtension_2525_ = lean_ctor_get(v_ext_2524_, 0);
v_asyncMode_2526_ = lean_ctor_get(v_toEnvExtension_2525_, 2);
v___x_2527_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref_n(v_env_2521_, 2);
v___x_2528_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2527_, v___x_2523_, v_env_2521_, v_asyncMode_2526_);
v_categories_2529_ = lean_ctor_get(v___x_2528_, 2);
lean_inc_ref(v_categories_2529_);
lean_dec(v___x_2528_);
lean_inc_ref(v_options_2522_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_env_2521_);
lean_ctor_set(v___x_2530_, 1, v_options_2522_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2531_, 0, v_categories_2529_);
lean_closure_set(v___f_2531_, 1, v_declName_2516_);
lean_closure_set(v___f_2531_, 2, v___x_2530_);
lean_closure_set(v___f_2531_, 3, v_ctx_2518_);
lean_closure_set(v___f_2531_, 4, v_s_2519_);
lean_closure_set(v___f_2531_, 5, v_evalFallback_x3f_2517_);
v___x_2532_ = l_unsafeBaseIO___redArg(v___f_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2533_, lean_object* v_decl_2534_, lean_object* v_ref_2535_){
_start:
{
lean_object* v_defValue_2537_; lean_object* v_descr_2538_; lean_object* v_deprecation_x3f_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v_defValue_2537_ = lean_ctor_get(v_decl_2534_, 0);
v_descr_2538_ = lean_ctor_get(v_decl_2534_, 1);
v_deprecation_x3f_2539_ = lean_ctor_get(v_decl_2534_, 2);
v___x_2540_ = lean_alloc_ctor(1, 0, 1);
v___x_2541_ = lean_unbox(v_defValue_2537_);
lean_ctor_set_uint8(v___x_2540_, 0, v___x_2541_);
lean_inc(v_deprecation_x3f_2539_);
lean_inc_ref(v_descr_2538_);
lean_inc_n(v_name_2533_, 2);
v___x_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2542_, 0, v_name_2533_);
lean_ctor_set(v___x_2542_, 1, v_ref_2535_);
lean_ctor_set(v___x_2542_, 2, v___x_2540_);
lean_ctor_set(v___x_2542_, 3, v_descr_2538_);
lean_ctor_set(v___x_2542_, 4, v_deprecation_x3f_2539_);
v___x_2543_ = lean_register_option(v_name_2533_, v___x_2542_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; 
v_unused_2552_ = lean_ctor_get(v___x_2543_, 0);
lean_dec(v_unused_2552_);
v___x_2545_ = v___x_2543_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_dec(v___x_2543_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_inc(v_defValue_2537_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_name_2533_);
lean_ctor_set(v___x_2547_, 1, v_defValue_2537_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_name_2533_);
v_a_2553_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2543_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2543_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2561_, lean_object* v_decl_2562_, lean_object* v_ref_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2561_, v_decl_2562_, v_ref_2563_);
lean_dec_ref(v_decl_2562_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2583_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2584_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2585_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2586_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2583_, v___x_2584_, v___x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2592_, lean_object* v_k_2593_, uint8_t v_v_2594_){
_start:
{
lean_object* v_map_2595_; uint8_t v_hasTrace_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2610_; 
v_map_2595_ = lean_ctor_get(v_o_2592_, 0);
v_hasTrace_2596_ = lean_ctor_get_uint8(v_o_2592_, sizeof(void*)*1);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_o_2592_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2598_ = v_o_2592_;
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_map_2595_);
lean_dec(v_o_2592_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2600_, 0, v_v_2594_);
lean_inc(v_k_2593_);
v___x_2601_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2593_, v___x_2600_, v_map_2595_);
if (v_hasTrace_2596_ == 0)
{
lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___x_2605_; 
v___x_2602_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2603_ = l_Lean_Name_isPrefixOf(v___x_2602_, v_k_2593_);
lean_dec(v_k_2593_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2605_ = v___x_2598_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2601_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*1, v___x_2603_);
return v___x_2605_;
}
}
else
{
lean_object* v___x_2608_; 
lean_dec(v_k_2593_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2608_ = v___x_2598_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2609_, sizeof(void*)*1, v_hasTrace_2596_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2611_, lean_object* v_k_2612_, lean_object* v_v_2613_){
_start:
{
uint8_t v_v_boxed_2614_; lean_object* v_res_2615_; 
v_v_boxed_2614_ = lean_unbox(v_v_2613_);
v_res_2615_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2611_, v_k_2612_, v_v_boxed_2614_);
return v_res_2615_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2616_, lean_object* v_opt_2617_){
_start:
{
lean_object* v_name_2618_; lean_object* v_defValue_2619_; lean_object* v_map_2620_; lean_object* v___x_2621_; 
v_name_2618_ = lean_ctor_get(v_opt_2617_, 0);
v_defValue_2619_ = lean_ctor_get(v_opt_2617_, 1);
v_map_2620_ = lean_ctor_get(v_opts_2616_, 0);
v___x_2621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2620_, v_name_2618_);
if (lean_obj_tag(v___x_2621_) == 0)
{
uint8_t v___x_2622_; 
v___x_2622_ = lean_unbox(v_defValue_2619_);
return v___x_2622_;
}
else
{
lean_object* v_val_2623_; 
v_val_2623_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v___x_2621_, 1);
if (lean_obj_tag(v_val_2623_) == 1)
{
uint8_t v_v_2624_; 
v_v_2624_ = lean_ctor_get_uint8(v_val_2623_, 0);
lean_dec_ref_known(v_val_2623_, 0);
return v_v_2624_;
}
else
{
uint8_t v___x_2625_; 
lean_dec(v_val_2623_);
v___x_2625_ = lean_unbox(v_defValue_2619_);
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2626_, lean_object* v_opt_2627_){
_start:
{
uint8_t v_res_2628_; lean_object* v_r_2629_; 
v_res_2628_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2626_, v_opt_2627_);
lean_dec_ref(v_opt_2627_);
lean_dec_ref(v_opts_2626_);
v_r_2629_ = lean_box(v_res_2628_);
return v_r_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(lean_object* v_ctx_2635_){
_start:
{
lean_object* v_toParserModuleContext_2636_; lean_object* v_toInputContext_2637_; lean_object* v_toCacheableParserContext_2638_; lean_object* v_tokens_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2660_; 
v_toParserModuleContext_2636_ = lean_ctor_get(v_ctx_2635_, 1);
v_toInputContext_2637_ = lean_ctor_get(v_ctx_2635_, 0);
v_toCacheableParserContext_2638_ = lean_ctor_get(v_ctx_2635_, 2);
v_tokens_2639_ = lean_ctor_get(v_ctx_2635_, 3);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_ctx_2635_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2641_ = v_ctx_2635_;
v_isShared_2642_ = v_isSharedCheck_2660_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_tokens_2639_);
lean_inc(v_toCacheableParserContext_2638_);
lean_inc(v_toParserModuleContext_2636_);
lean_inc(v_toInputContext_2637_);
lean_dec(v_ctx_2635_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2660_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_env_2643_; lean_object* v_options_2644_; lean_object* v_currNamespace_2645_; lean_object* v_openDecls_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2659_; 
v_env_2643_ = lean_ctor_get(v_toParserModuleContext_2636_, 0);
v_options_2644_ = lean_ctor_get(v_toParserModuleContext_2636_, 1);
v_currNamespace_2645_ = lean_ctor_get(v_toParserModuleContext_2636_, 2);
v_openDecls_2646_ = lean_ctor_get(v_toParserModuleContext_2636_, 3);
v_isSharedCheck_2659_ = !lean_is_exclusive(v_toParserModuleContext_2636_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2648_ = v_toParserModuleContext_2636_;
v_isShared_2649_ = v_isSharedCheck_2659_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_openDecls_2646_);
lean_inc(v_currNamespace_2645_);
lean_inc(v_options_2644_);
lean_inc(v_env_2643_);
lean_dec(v_toParserModuleContext_2636_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2659_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2650_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2651_ = 0;
v___x_2652_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2644_, v___x_2650_, v___x_2651_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v___x_2652_);
v___x_2654_ = v___x_2648_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_env_2643_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v_currNamespace_2645_);
lean_ctor_set(v_reuseFailAlloc_2658_, 3, v_openDecls_2646_);
v___x_2654_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2656_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v___x_2654_);
v___x_2656_ = v___x_2641_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_toInputContext_2637_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v_toCacheableParserContext_2638_);
lean_ctor_set(v_reuseFailAlloc_2657_, 3, v_tokens_2639_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2661_, lean_object* v_declName_2662_, lean_object* v___f_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_toParserModuleContext_2666_; lean_object* v_toCacheableParserContext_2667_; uint8_t v___y_2669_; lean_object* v_quotDepth_2681_; uint8_t v_suppressInsideQuot_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v_toParserModuleContext_2666_ = lean_ctor_get(v___y_2664_, 1);
v_toCacheableParserContext_2667_ = lean_ctor_get(v___y_2664_, 2);
v_quotDepth_2681_ = lean_ctor_get(v_toCacheableParserContext_2667_, 1);
v_suppressInsideQuot_2682_ = lean_ctor_get_uint8(v_toCacheableParserContext_2667_, sizeof(void*)*4);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_nat_dec_lt(v___x_2683_, v_quotDepth_2681_);
if (v___x_2684_ == 0)
{
v___y_2669_ = v___x_2684_;
goto v___jp_2668_;
}
else
{
if (v_suppressInsideQuot_2682_ == 0)
{
v___y_2669_ = v___x_2684_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2685_; 
lean_dec_ref(v___f_2663_);
lean_dec(v_declName_2662_);
v___x_2685_ = lean_apply_2(v_fn_2661_, v___y_2664_, v___y_2665_);
return v___x_2685_;
}
}
v___jp_2668_:
{
if (v___y_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_dec_ref(v___f_2663_);
lean_dec(v_declName_2662_);
v___x_2670_ = lean_apply_2(v_fn_2661_, v___y_2664_, v___y_2665_);
return v___x_2670_;
}
else
{
lean_object* v_env_2671_; lean_object* v_options_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v_env_2671_ = lean_ctor_get(v_toParserModuleContext_2666_, 0);
v_options_2672_ = lean_ctor_get(v_toParserModuleContext_2666_, 1);
v___x_2673_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2674_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2672_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec_ref(v___f_2663_);
lean_dec(v_declName_2662_);
v___x_2675_ = lean_apply_2(v_fn_2661_, v___y_2664_, v___y_2665_);
return v___x_2675_;
}
else
{
uint8_t v___x_2676_; 
lean_inc(v_declName_2662_);
lean_inc_ref(v_env_2671_);
v___x_2676_ = l_Lean_Environment_contains(v_env_2671_, v_declName_2662_, v___x_2674_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
lean_dec_ref(v___f_2663_);
lean_dec(v_declName_2662_);
v___x_2677_ = lean_apply_2(v_fn_2661_, v___y_2664_, v___y_2665_);
return v___x_2677_;
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_fn_2661_);
v___x_2679_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2679_, 0, v_declName_2662_);
lean_closure_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2663_, v___x_2679_, v___y_2664_, v___y_2665_);
return v___x_2680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2687_, lean_object* v_p_2688_){
_start:
{
lean_object* v_info_2689_; lean_object* v_fn_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2699_; 
v_info_2689_ = lean_ctor_get(v_p_2688_, 0);
v_fn_2690_ = lean_ctor_get(v_p_2688_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_p_2688_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2692_ = v_p_2688_;
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_fn_2690_);
lean_inc(v_info_2689_);
lean_dec(v_p_2688_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___x_2697_; 
v___f_2694_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___closed__0));
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 5, 3);
lean_closure_set(v___f_2695_, 0, v_fn_2690_);
lean_closure_set(v___f_2695_, 1, v_declName_2687_);
lean_closure_set(v___f_2695_, 2, v___f_2694_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 1, v___f_2695_);
v___x_2697_ = v___x_2692_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_info_2689_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___f_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2700_, lean_object* v_declName_2701_, uint8_t v_leading_2702_, lean_object* v_p_2703_, lean_object* v_prio_2704_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v_p_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2706_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2707_ = lean_st_ref_get(v___x_2706_);
lean_inc_n(v_declName_2701_, 2);
v_p_2708_ = l_Lean_Parser_evalInsideQuot(v_declName_2701_, v_p_2703_);
lean_inc_ref(v_p_2708_);
v___x_2709_ = l_Lean_Parser_addParser(v___x_2707_, v_catName_2700_, v_declName_2701_, v_leading_2702_, v_p_2708_, v_prio_2704_);
v___x_2710_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2709_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v_info_2715_; lean_object* v_collectKinds_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = lean_st_ref_swap(v___x_2706_, v_a_2711_);
lean_dec(v___x_2712_);
v___x_2713_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2714_ = lean_st_ref_take(v___x_2713_);
v_info_2715_ = lean_ctor_get(v_p_2708_, 0);
lean_inc_ref(v_info_2715_);
lean_dec_ref(v_p_2708_);
v_collectKinds_2716_ = lean_ctor_get(v_info_2715_, 1);
lean_inc_ref(v_collectKinds_2716_);
v___x_2717_ = lean_apply_1(v_collectKinds_2716_, v___x_2714_);
v___x_2718_ = lean_st_ref_put(v___x_2713_, v___x_2717_);
v___x_2719_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2715_, v_declName_2701_);
return v___x_2719_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v_p_2708_);
lean_dec(v_declName_2701_);
v_a_2720_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2710_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2710_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2728_, lean_object* v_declName_2729_, lean_object* v_leading_2730_, lean_object* v_p_2731_, lean_object* v_prio_2732_, lean_object* v_a_2733_){
_start:
{
uint8_t v_leading_boxed_2734_; lean_object* v_res_2735_; 
v_leading_boxed_2734_ = lean_unbox(v_leading_2730_);
v_res_2735_ = l_Lean_Parser_addBuiltinParser(v_catName_2728_, v_declName_2729_, v_leading_boxed_2734_, v_p_2731_, v_prio_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2736_, lean_object* v_declName_2737_, lean_object* v_p_2738_, lean_object* v_prio_2739_){
_start:
{
uint8_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = 1;
v___x_2742_ = l_Lean_Parser_addBuiltinParser(v_catName_2736_, v_declName_2737_, v___x_2741_, v_p_2738_, v_prio_2739_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2743_, lean_object* v_declName_2744_, lean_object* v_p_2745_, lean_object* v_prio_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2743_, v_declName_2744_, v_p_2745_, v_prio_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2749_, lean_object* v_declName_2750_, lean_object* v_p_2751_, lean_object* v_prio_2752_){
_start:
{
uint8_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = 0;
v___x_2755_ = l_Lean_Parser_addBuiltinParser(v_catName_2749_, v_declName_2750_, v___x_2754_, v_p_2751_, v_prio_2752_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2756_, lean_object* v_declName_2757_, lean_object* v_p_2758_, lean_object* v_prio_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2756_, v_declName_2757_, v_p_2758_, v_prio_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2762_){
_start:
{
uint8_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = 1;
lean_inc(v_kind_2762_);
v___x_2764_ = l_Lean_Name_toString(v_kind_2762_, v___x_2763_);
v___x_2765_ = l_Lean_Parser_mkAntiquot(v___x_2764_, v_kind_2762_, v___x_2763_, v___x_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2769_; lean_object* v_fn_2770_; lean_object* v___x_2771_; 
v___x_2769_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2766_);
v_fn_2770_ = lean_ctor_get(v___x_2769_, 1);
lean_inc_ref(v_fn_2770_);
lean_dec_ref(v___x_2769_);
v___x_2771_ = lean_apply_2(v_fn_2770_, v_a_2767_, v_a_2768_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v_fn_2776_; lean_object* v___x_2777_; 
v___x_2775_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2772_);
v_fn_2776_ = lean_ctor_get(v___x_2775_, 1);
lean_inc_ref(v_fn_2776_);
lean_dec_ref(v___x_2775_);
v___x_2777_ = lean_apply_2(v_fn_2776_, v___y_2773_, v___y_2774_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2786_, lean_object* v_ctx_2787_, lean_object* v_s_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; uint8_t v___x_2792_; lean_object* v___y_2794_; 
v___x_2789_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2790_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2791_ = lean_name_eq(v_catName_2786_, v___x_2790_);
v___x_2792_ = 1;
if (v___x_2791_ == 0)
{
v___y_2794_ = v_catName_2786_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2816_; 
lean_dec(v_catName_2786_);
v___x_2816_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2794_ = v___x_2816_;
goto v___jp_2793_;
}
v___jp_2793_:
{
lean_object* v_toParserModuleContext_2795_; lean_object* v_env_2796_; lean_object* v___x_2797_; lean_object* v_ext_2798_; lean_object* v_toEnvExtension_2799_; lean_object* v_asyncMode_2800_; lean_object* v___x_2801_; lean_object* v_categories_2802_; lean_object* v___x_2803_; 
v_toParserModuleContext_2795_ = lean_ctor_get(v_ctx_2787_, 1);
v_env_2796_ = lean_ctor_get(v_toParserModuleContext_2795_, 0);
v___x_2797_ = l_Lean_Parser_parserExtension;
v_ext_2798_ = lean_ctor_get(v___x_2797_, 1);
v_toEnvExtension_2799_ = lean_ctor_get(v_ext_2798_, 0);
v_asyncMode_2800_ = lean_ctor_get(v_toEnvExtension_2799_, 2);
lean_inc_ref(v_env_2796_);
v___x_2801_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2789_, v___x_2797_, v_env_2796_, v_asyncMode_2800_);
v_categories_2802_ = lean_ctor_get(v___x_2801_, 2);
lean_inc_ref(v_categories_2802_);
lean_dec(v___x_2801_);
v___x_2803_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2802_, v___y_2794_);
lean_dec_ref(v_categories_2802_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_dec_ref(v_ctx_2787_);
v___x_2804_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2805_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2794_, v___x_2792_);
v___x_2806_ = lean_string_append(v___x_2804_, v___x_2805_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2808_ = lean_string_append(v___x_2806_, v___x_2807_);
v___x_2809_ = lean_box(0);
v___x_2810_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2788_, v___x_2808_, v___x_2809_, v___x_2792_);
return v___x_2810_;
}
else
{
lean_object* v_val_2811_; lean_object* v_tables_2812_; uint8_t v_behavior_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; 
v_val_2811_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_val_2811_);
lean_dec_ref_known(v___x_2803_, 1);
v_tables_2812_ = lean_ctor_get(v_val_2811_, 2);
lean_inc_ref(v_tables_2812_);
v_behavior_2813_ = lean_ctor_get_uint8(v_val_2811_, sizeof(void*)*3);
lean_dec(v_val_2811_);
lean_inc(v___y_2794_);
v___f_2814_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2814_, 0, v___y_2794_);
v___x_2815_ = l_Lean_Parser_prattParser(v___y_2794_, v_tables_2812_, v_behavior_2813_, v___f_2814_, v_ctx_2787_, v_s_2788_);
return v___x_2815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2819_ = l_Lean_Parser_categoryParserFnRef;
v___x_2820_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2821_ = lean_st_ref_swap(v___x_2819_, v___x_2820_);
lean_dec(v___x_2821_);
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2825_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2826_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2831_, lean_object* v_b_2832_, uint8_t v_kind_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_currNamespace_2837_; lean_object* v___x_2838_; lean_object* v_env_2839_; lean_object* v_nextMacroScope_2840_; lean_object* v_ngen_2841_; lean_object* v_auxDeclNGen_2842_; lean_object* v_traceState_2843_; lean_object* v_messages_2844_; lean_object* v_infoState_2845_; lean_object* v_snapshotTasks_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2858_; 
v_currNamespace_2837_ = lean_ctor_get(v___y_2834_, 6);
v___x_2838_ = lean_st_ref_take(v___y_2835_);
v_env_2839_ = lean_ctor_get(v___x_2838_, 0);
v_nextMacroScope_2840_ = lean_ctor_get(v___x_2838_, 1);
v_ngen_2841_ = lean_ctor_get(v___x_2838_, 2);
v_auxDeclNGen_2842_ = lean_ctor_get(v___x_2838_, 3);
v_traceState_2843_ = lean_ctor_get(v___x_2838_, 4);
v_messages_2844_ = lean_ctor_get(v___x_2838_, 6);
v_infoState_2845_ = lean_ctor_get(v___x_2838_, 7);
v_snapshotTasks_2846_ = lean_ctor_get(v___x_2838_, 8);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2838_, 5);
lean_dec(v_unused_2859_);
v___x_2848_ = v___x_2838_;
v_isShared_2849_ = v_isSharedCheck_2858_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_snapshotTasks_2846_);
lean_inc(v_infoState_2845_);
lean_inc(v_messages_2844_);
lean_inc(v_traceState_2843_);
lean_inc(v_auxDeclNGen_2842_);
lean_inc(v_ngen_2841_);
lean_inc(v_nextMacroScope_2840_);
lean_inc(v_env_2839_);
lean_dec(v___x_2838_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2858_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_inc(v_currNamespace_2837_);
v___x_2850_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2839_, v_ext_2831_, v_b_2832_, v_kind_2833_, v_currNamespace_2837_);
v___x_2851_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 5, v___x_2851_);
lean_ctor_set(v___x_2848_, 0, v___x_2850_);
v___x_2853_ = v___x_2848_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_nextMacroScope_2840_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_ngen_2841_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_auxDeclNGen_2842_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_traceState_2843_);
lean_ctor_set(v_reuseFailAlloc_2857_, 5, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2857_, 6, v_messages_2844_);
lean_ctor_set(v_reuseFailAlloc_2857_, 7, v_infoState_2845_);
lean_ctor_set(v_reuseFailAlloc_2857_, 8, v_snapshotTasks_2846_);
v___x_2853_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2854_ = lean_st_ref_put(v___y_2835_, v___x_2853_);
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2860_, lean_object* v_b_2861_, lean_object* v_kind_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
uint8_t v_kind_boxed_2866_; lean_object* v_res_2867_; 
v_kind_boxed_2866_ = lean_unbox(v_kind_2862_);
v_res_2867_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2860_, v_b_2861_, v_kind_boxed_2866_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2868_, lean_object* v_00_u03b2_2869_, lean_object* v_00_u03c3_2870_, lean_object* v_ext_2871_, lean_object* v_b_2872_, uint8_t v_kind_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2871_, v_b_2872_, v_kind_2873_, v___y_2874_, v___y_2875_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2878_, lean_object* v_00_u03b2_2879_, lean_object* v_00_u03c3_2880_, lean_object* v_ext_2881_, lean_object* v_b_2882_, lean_object* v_kind_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v_kind_boxed_2887_; lean_object* v_res_2888_; 
v_kind_boxed_2887_ = lean_unbox(v_kind_2883_);
v_res_2888_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2878_, v_00_u03b2_2879_, v_00_u03c3_2880_, v_ext_2881_, v_b_2882_, v_kind_boxed_2887_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2893_ = lean_ctor_get(v_x_2889_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v_x_2889_, 1);
v___x_2894_ = l_Lean_stringToMessageData(v_a_2893_);
v___x_2895_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2894_, v___y_2890_, v___y_2891_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_a_2896_ = lean_ctor_get(v_x_2889_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_x_2889_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v_x_2889_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v_x_2889_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set_tag(v___x_2898_, 0);
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2909_, uint8_t v_kind_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v___x_2914_; lean_object* v_env_2915_; lean_object* v___x_2916_; lean_object* v_ext_2917_; lean_object* v_toEnvExtension_2918_; lean_object* v_asyncMode_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v_tokens_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2914_ = lean_st_ref_get(v_a_2912_);
v_env_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc_ref(v_env_2915_);
lean_dec(v___x_2914_);
v___x_2916_ = l_Lean_Parser_parserExtension;
v_ext_2917_ = lean_ctor_get(v___x_2916_, 1);
v_toEnvExtension_2918_ = lean_ctor_get(v_ext_2917_, 0);
v_asyncMode_2919_ = lean_ctor_get(v_toEnvExtension_2918_, 2);
v___x_2920_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2921_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2920_, v___x_2916_, v_env_2915_, v_asyncMode_2919_);
v_tokens_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc_ref(v_tokens_2922_);
lean_dec(v___x_2921_);
lean_inc_ref(v_tk_2909_);
v___x_2923_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2922_, v_tk_2909_);
v___x_2924_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2923_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec_ref_known(v___x_2924_, 1);
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_tk_2909_);
v___x_2926_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2916_, v___x_2925_, v_kind_2910_, v_a_2911_, v_a_2912_);
return v___x_2926_;
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v_tk_2909_);
v_a_2927_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2924_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2924_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_2935_, lean_object* v_kind_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
uint8_t v_kind_boxed_2940_; lean_object* v_res_2941_; 
v_kind_boxed_2940_ = lean_unbox(v_kind_2936_);
v_res_2941_ = l_Lean_Parser_addToken(v_tk_2935_, v_kind_boxed_2940_, v_a_2937_, v_a_2938_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_2942_, lean_object* v_x_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2943_, v___y_2944_, v___y_2945_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_2948_, lean_object* v_x_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_2948_, v_x_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_2954_, lean_object* v_k_2955_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = l_Lean_Parser_parserExtension;
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_k_2955_);
v___x_2958_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2956_, v_env_2954_, v___x_2957_);
return v___x_2958_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_internal_is_stage0(v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_2961_, lean_object* v_k_2962_){
_start:
{
lean_object* v___x_2963_; lean_object* v_ext_2964_; lean_object* v_toEnvExtension_2965_; lean_object* v_asyncMode_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_kinds_2969_; uint8_t v___x_2970_; 
v___x_2963_ = l_Lean_Parser_parserExtension;
v_ext_2964_ = lean_ctor_get(v___x_2963_, 1);
v_toEnvExtension_2965_ = lean_ctor_get(v_ext_2964_, 0);
v_asyncMode_2966_ = lean_ctor_get(v_toEnvExtension_2965_, 2);
v___x_2967_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2961_);
v___x_2968_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2967_, v___x_2963_, v_env_2961_, v_asyncMode_2966_);
v_kinds_2969_ = lean_ctor_get(v___x_2968_, 1);
lean_inc_ref(v_kinds_2969_);
lean_dec(v___x_2968_);
v___x_2970_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2969_, v_k_2962_);
lean_dec_ref(v_kinds_2969_);
if (v___x_2970_ == 0)
{
uint8_t v___x_2971_; 
v___x_2971_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_2971_ == 0)
{
lean_dec(v_k_2962_);
lean_dec_ref(v_env_2961_);
return v___x_2971_;
}
else
{
uint8_t v___x_2972_; 
v___x_2972_ = l_Lean_Environment_contains(v_env_2961_, v_k_2962_, v___x_2971_);
return v___x_2972_;
}
}
else
{
lean_dec(v_k_2962_);
lean_dec_ref(v_env_2961_);
return v___x_2970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_2973_, lean_object* v_k_2974_){
_start:
{
uint8_t v_res_2975_; lean_object* v_r_2976_; 
v_res_2975_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2973_, v_k_2974_);
v_r_2976_ = lean_box(v_res_2975_);
return v_r_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_2977_, lean_object* v_k_2978_, lean_object* v_x_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2980_, 0, v_k_2978_);
lean_ctor_set(v___x_2980_, 1, v_ks_2977_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2981_, lean_object* v_keys_2982_, lean_object* v_vals_2983_, lean_object* v_i_2984_, lean_object* v_acc_2985_){
_start:
{
lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2986_ = lean_array_get_size(v_keys_2982_);
v___x_2987_ = lean_nat_dec_lt(v_i_2984_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_dec(v_i_2984_);
lean_dec(v_f_2981_);
return v_acc_2985_;
}
else
{
lean_object* v_k_2988_; lean_object* v_v_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_k_2988_ = lean_array_fget_borrowed(v_keys_2982_, v_i_2984_);
v_v_2989_ = lean_array_fget_borrowed(v_vals_2983_, v_i_2984_);
lean_inc(v_f_2981_);
lean_inc(v_v_2989_);
lean_inc(v_k_2988_);
v___x_2990_ = lean_apply_3(v_f_2981_, v_acc_2985_, v_k_2988_, v_v_2989_);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_i_2984_, v___x_2991_);
lean_dec(v_i_2984_);
v_i_2984_ = v___x_2992_;
v_acc_2985_ = v___x_2990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2994_, lean_object* v_keys_2995_, lean_object* v_vals_2996_, lean_object* v_i_2997_, lean_object* v_acc_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2994_, v_keys_2995_, v_vals_2996_, v_i_2997_, v_acc_2998_);
lean_dec_ref(v_vals_2996_);
lean_dec_ref(v_keys_2995_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3000_, lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
if (lean_obj_tag(v_x_3001_) == 0)
{
lean_object* v_es_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v_es_3003_ = lean_ctor_get(v_x_3001_, 0);
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = lean_array_get_size(v_es_3003_);
v___x_3006_ = lean_nat_dec_lt(v___x_3004_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_dec(v_f_3000_);
return v_x_3002_;
}
else
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_nat_dec_le(v___x_3005_, v___x_3005_);
if (v___x_3007_ == 0)
{
if (v___x_3006_ == 0)
{
lean_dec(v_f_3000_);
return v_x_3002_;
}
else
{
size_t v___x_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = lean_usize_of_nat(v___x_3005_);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3000_, v_es_3003_, v___x_3008_, v___x_3009_, v_x_3002_);
return v___x_3010_;
}
}
else
{
size_t v___x_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = ((size_t)0ULL);
v___x_3012_ = lean_usize_of_nat(v___x_3005_);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3000_, v_es_3003_, v___x_3011_, v___x_3012_, v_x_3002_);
return v___x_3013_;
}
}
}
else
{
lean_object* v_ks_3014_; lean_object* v_vs_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_ks_3014_ = lean_ctor_get(v_x_3001_, 0);
v_vs_3015_ = lean_ctor_get(v_x_3001_, 1);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3000_, v_ks_3014_, v_vs_3015_, v___x_3016_, v_x_3002_);
return v___x_3017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3018_, lean_object* v_as_3019_, size_t v_i_3020_, size_t v_stop_3021_, lean_object* v_b_3022_){
_start:
{
lean_object* v___y_3024_; uint8_t v___x_3028_; 
v___x_3028_ = lean_usize_dec_eq(v_i_3020_, v_stop_3021_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_array_uget_borrowed(v_as_3019_, v_i_3020_);
switch(lean_obj_tag(v___x_3029_))
{
case 0:
{
lean_object* v_key_3030_; lean_object* v_val_3031_; lean_object* v___x_3032_; 
v_key_3030_ = lean_ctor_get(v___x_3029_, 0);
v_val_3031_ = lean_ctor_get(v___x_3029_, 1);
lean_inc(v_f_3018_);
lean_inc(v_val_3031_);
lean_inc(v_key_3030_);
v___x_3032_ = lean_apply_3(v_f_3018_, v_b_3022_, v_key_3030_, v_val_3031_);
v___y_3024_ = v___x_3032_;
goto v___jp_3023_;
}
case 1:
{
lean_object* v_node_3033_; lean_object* v___x_3034_; 
v_node_3033_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_f_3018_);
v___x_3034_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3018_, v_node_3033_, v_b_3022_);
v___y_3024_ = v___x_3034_;
goto v___jp_3023_;
}
default: 
{
v___y_3024_ = v_b_3022_;
goto v___jp_3023_;
}
}
}
else
{
lean_dec(v_f_3018_);
return v_b_3022_;
}
v___jp_3023_:
{
size_t v___x_3025_; size_t v___x_3026_; 
v___x_3025_ = ((size_t)1ULL);
v___x_3026_ = lean_usize_add(v_i_3020_, v___x_3025_);
v_i_3020_ = v___x_3026_;
v_b_3022_ = v___y_3024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3035_, lean_object* v_as_3036_, lean_object* v_i_3037_, lean_object* v_stop_3038_, lean_object* v_b_3039_){
_start:
{
size_t v_i_boxed_3040_; size_t v_stop_boxed_3041_; lean_object* v_res_3042_; 
v_i_boxed_3040_ = lean_unbox_usize(v_i_3037_);
lean_dec(v_i_3037_);
v_stop_boxed_3041_ = lean_unbox_usize(v_stop_3038_);
lean_dec(v_stop_3038_);
v_res_3042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3035_, v_as_3036_, v_i_boxed_3040_, v_stop_boxed_3041_, v_b_3039_);
lean_dec_ref(v_as_3036_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3043_, lean_object* v_x_3044_, lean_object* v_x_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3043_, v_x_3044_, v_x_3045_);
lean_dec_ref(v_x_3044_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3047_, lean_object* v_x1_3048_, lean_object* v_x2_3049_, lean_object* v_x3_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_apply_3(v_f_3047_, v_x1_3048_, v_x2_3049_, v_x3_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3052_, lean_object* v_f_3053_, lean_object* v_init_3054_){
_start:
{
lean_object* v___f_3055_; lean_object* v___x_3056_; 
v___f_3055_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3055_, 0, v_f_3053_);
v___x_3056_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3055_, v_map_3052_, v_init_3054_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3057_, lean_object* v_f_3058_, lean_object* v_init_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3057_, v_f_3058_, v_init_3059_);
lean_dec_ref(v_map_3057_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3062_){
_start:
{
lean_object* v___x_3063_; lean_object* v_ext_3064_; lean_object* v_toEnvExtension_3065_; lean_object* v_asyncMode_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v_kinds_3069_; lean_object* v___f_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3063_ = l_Lean_Parser_parserExtension;
v_ext_3064_ = lean_ctor_get(v___x_3063_, 1);
v_toEnvExtension_3065_ = lean_ctor_get(v_ext_3064_, 0);
v_asyncMode_3066_ = lean_ctor_get(v_toEnvExtension_3065_, 2);
v___x_3067_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3068_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3067_, v___x_3063_, v_env_3062_, v_asyncMode_3066_);
v_kinds_3069_ = lean_ctor_get(v___x_3068_, 1);
lean_inc_ref(v_kinds_3069_);
lean_dec(v___x_3068_);
v___f_3070_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3071_ = lean_box(0);
v___x_3072_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3069_, v___f_3070_, v___x_3071_);
lean_dec_ref(v_kinds_3069_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3073_, lean_object* v_00_u03b2_3074_, lean_object* v_map_3075_, lean_object* v_f_3076_, lean_object* v_init_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3075_, v_f_3076_, v_init_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3079_, lean_object* v_00_u03b2_3080_, lean_object* v_map_3081_, lean_object* v_f_3082_, lean_object* v_init_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3079_, v_00_u03b2_3080_, v_map_3081_, v_f_3082_, v_init_3083_);
lean_dec_ref(v_map_3081_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3085_, lean_object* v_f_3086_, lean_object* v_init_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3086_, v_map_3085_, v_init_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3089_, lean_object* v_f_3090_, lean_object* v_init_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3089_, v_f_3090_, v_init_3091_);
lean_dec_ref(v_map_3089_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_map_3095_, lean_object* v_f_3096_, lean_object* v_init_3097_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3096_, v_map_3095_, v_init_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3099_, lean_object* v_00_u03b2_3100_, lean_object* v_map_3101_, lean_object* v_f_3102_, lean_object* v_init_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3099_, v_00_u03b2_3100_, v_map_3101_, v_f_3102_, v_init_3103_);
lean_dec_ref(v_map_3101_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3105_, lean_object* v_00_u03b1_3106_, lean_object* v_00_u03b2_3107_, lean_object* v_f_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3108_, v_x_3109_, v_x_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3112_, lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_f_3115_, lean_object* v_x_3116_, lean_object* v_x_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3112_, v_00_u03b1_3113_, v_00_u03b2_3114_, v_f_3115_, v_x_3116_, v_x_3117_);
lean_dec_ref(v_x_3116_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3119_, lean_object* v_00_u03b2_3120_, lean_object* v_00_u03c3_3121_, lean_object* v_f_3122_, lean_object* v_as_3123_, size_t v_i_3124_, size_t v_stop_3125_, lean_object* v_b_3126_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3122_, v_as_3123_, v_i_3124_, v_stop_3125_, v_b_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3128_, lean_object* v_00_u03b2_3129_, lean_object* v_00_u03c3_3130_, lean_object* v_f_3131_, lean_object* v_as_3132_, lean_object* v_i_3133_, lean_object* v_stop_3134_, lean_object* v_b_3135_){
_start:
{
size_t v_i_boxed_3136_; size_t v_stop_boxed_3137_; lean_object* v_res_3138_; 
v_i_boxed_3136_ = lean_unbox_usize(v_i_3133_);
lean_dec(v_i_3133_);
v_stop_boxed_3137_ = lean_unbox_usize(v_stop_3134_);
lean_dec(v_stop_3134_);
v_res_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3128_, v_00_u03b2_3129_, v_00_u03c3_3130_, v_f_3131_, v_as_3132_, v_i_boxed_3136_, v_stop_boxed_3137_, v_b_3135_);
lean_dec_ref(v_as_3132_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3139_, lean_object* v_00_u03b1_3140_, lean_object* v_00_u03b2_3141_, lean_object* v_f_3142_, lean_object* v_keys_3143_, lean_object* v_vals_3144_, lean_object* v_heq_3145_, lean_object* v_i_3146_, lean_object* v_acc_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3142_, v_keys_3143_, v_vals_3144_, v_i_3146_, v_acc_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3149_, lean_object* v_00_u03b1_3150_, lean_object* v_00_u03b2_3151_, lean_object* v_f_3152_, lean_object* v_keys_3153_, lean_object* v_vals_3154_, lean_object* v_heq_3155_, lean_object* v_i_3156_, lean_object* v_acc_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3149_, v_00_u03b1_3150_, v_00_u03b2_3151_, v_f_3152_, v_keys_3153_, v_vals_3154_, v_heq_3155_, v_i_3156_, v_acc_3157_);
lean_dec_ref(v_vals_3154_);
lean_dec_ref(v_keys_3153_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3159_){
_start:
{
lean_object* v___x_3160_; lean_object* v_ext_3161_; lean_object* v_toEnvExtension_3162_; lean_object* v_asyncMode_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v_tokens_3166_; 
v___x_3160_ = l_Lean_Parser_parserExtension;
v_ext_3161_ = lean_ctor_get(v___x_3160_, 1);
v_toEnvExtension_3162_ = lean_ctor_get(v_ext_3161_, 0);
v_asyncMode_3163_ = lean_ctor_get(v_toEnvExtension_3162_, 2);
v___x_3164_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3165_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3164_, v___x_3160_, v_env_3159_, v_asyncMode_3163_);
v_tokens_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc_ref(v_tokens_3166_);
lean_dec(v___x_3165_);
return v_tokens_3166_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3192_ = l_Lean_mkAtom(v___x_3191_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3194_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3195_ = lean_array_push(v___x_3194_, v___x_3193_);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3207_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3208_ = lean_array_push(v___x_3207_, v___x_3206_);
return v___x_3208_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3209_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3210_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3211_ = lean_box(2);
v___x_3212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v___x_3210_);
lean_ctor_set(v___x_3212_, 2, v___x_3209_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3214_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3215_ = lean_array_push(v___x_3214_, v___x_3213_);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3217_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3218_ = lean_array_push(v___x_3217_, v___x_3216_);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3219_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3220_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3221_ = lean_array_push(v___x_3220_, v___x_3219_);
return v___x_3221_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3223_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3224_ = lean_array_push(v___x_3223_, v___x_3222_);
return v___x_3224_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3225_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3226_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3227_ = lean_array_push(v___x_3226_, v___x_3225_);
return v___x_3227_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3228_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3229_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3230_ = lean_box(2);
v___x_3231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
lean_ctor_set(v___x_3231_, 2, v___x_3228_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3233_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3234_ = lean_array_push(v___x_3233_, v___x_3232_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3235_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3236_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3237_ = lean_box(2);
v___x_3238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
lean_ctor_set(v___x_3238_, 1, v___x_3236_);
lean_ctor_set(v___x_3238_, 2, v___x_3235_);
return v___x_3238_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3240_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3241_ = lean_array_push(v___x_3240_, v___x_3239_);
return v___x_3241_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3242_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3243_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3244_ = lean_box(2);
v___x_3245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v___x_3243_);
lean_ctor_set(v___x_3245_, 2, v___x_3242_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3247_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3248_ = lean_array_push(v___x_3247_, v___x_3246_);
return v___x_3248_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3249_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3250_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3251_ = lean_box(2);
v___x_3252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3250_);
lean_ctor_set(v___x_3252_, 2, v___x_3249_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3254_, lean_object* v_fileName_3255_, uint8_t v_normalizeLineEndings_3256_, lean_object* v_endPos_3257_){
_start:
{
lean_object* v_fst_3259_; lean_object* v_snd_3260_; lean_object* v_text_3266_; 
v_text_3266_ = l_Lean_FileMap_ofString(v_input_3254_);
if (v_normalizeLineEndings_3256_ == 0)
{
v_fst_3259_ = v_text_3266_;
v_snd_3260_ = v_endPos_3257_;
goto v___jp_3258_;
}
else
{
lean_object* v_source_3267_; lean_object* v_endPos_x27_3268_; lean_object* v___x_3269_; lean_object* v_text_3270_; lean_object* v___x_3271_; 
v_source_3267_ = lean_ctor_get(v_text_3266_, 0);
lean_inc_ref(v_source_3267_);
v_endPos_x27_3268_ = l_Lean_FileMap_toPosition(v_text_3266_, v_endPos_3257_);
lean_dec(v_endPos_3257_);
v___x_3269_ = l_String_crlfToLf(v_source_3267_);
lean_dec_ref(v_source_3267_);
v_text_3270_ = l_Lean_FileMap_ofString(v___x_3269_);
v___x_3271_ = l_Lean_FileMap_ofPosition(v_text_3270_, v_endPos_x27_3268_);
v_fst_3259_ = v_text_3270_;
v_snd_3260_ = v___x_3271_;
goto v___jp_3258_;
}
v___jp_3258_:
{
lean_object* v_source_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v_source_3261_ = lean_ctor_get(v_fst_3259_, 0);
lean_inc_ref(v_source_3261_);
v___x_3262_ = lean_string_utf8_byte_size(v_source_3261_);
v___x_3263_ = lean_nat_dec_le(v_snd_3260_, v___x_3262_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; 
lean_dec(v_snd_3260_);
v___x_3264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3264_, 0, v_source_3261_);
lean_ctor_set(v___x_3264_, 1, v_fileName_3255_);
lean_ctor_set(v___x_3264_, 2, v_fst_3259_);
lean_ctor_set(v___x_3264_, 3, v___x_3262_);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; 
v___x_3265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3265_, 0, v_source_3261_);
lean_ctor_set(v___x_3265_, 1, v_fileName_3255_);
lean_ctor_set(v___x_3265_, 2, v_fst_3259_);
lean_ctor_set(v___x_3265_, 3, v_snd_3260_);
return v___x_3265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3272_, lean_object* v_fileName_3273_, lean_object* v_normalizeLineEndings_3274_, lean_object* v_endPos_3275_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3276_; lean_object* v_res_3277_; 
v_normalizeLineEndings_boxed_3276_ = lean_unbox(v_normalizeLineEndings_3274_);
v_res_3277_ = l_Lean_Parser_mkInputContext___redArg(v_input_3272_, v_fileName_3273_, v_normalizeLineEndings_boxed_3276_, v_endPos_3275_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3278_, lean_object* v_fileName_3279_, uint8_t v_normalizeLineEndings_3280_, lean_object* v_endPos_3281_, lean_object* v_endPos__valid_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Parser_mkInputContext___redArg(v_input_3278_, v_fileName_3279_, v_normalizeLineEndings_3280_, v_endPos_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3284_, lean_object* v_fileName_3285_, lean_object* v_normalizeLineEndings_3286_, lean_object* v_endPos_3287_, lean_object* v_endPos__valid_3288_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3289_; lean_object* v_res_3290_; 
v_normalizeLineEndings_boxed_3289_ = lean_unbox(v_normalizeLineEndings_3286_);
v_res_3290_ = l_Lean_Parser_mkInputContext(v_input_3284_, v_fileName_3285_, v_normalizeLineEndings_boxed_3289_, v_endPos_3287_, v_endPos__valid_3288_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3293_){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3294_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = l_Lean_Parser_initCacheForInput(v_input_3293_);
v___x_3297_ = lean_box(0);
v___x_3298_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3299_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3294_);
lean_ctor_set(v___x_3299_, 1, v___x_3295_);
lean_ctor_set(v___x_3299_, 2, v___x_3295_);
lean_ctor_set(v___x_3299_, 3, v___x_3296_);
lean_ctor_set(v___x_3299_, 4, v___x_3297_);
lean_ctor_set(v___x_3299_, 5, v___x_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Parser_mkParserState(v_input_3300_);
lean_dec_ref(v_input_3300_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3304_, lean_object* v_catName_3305_, lean_object* v_input_3306_, lean_object* v_fileName_3307_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v_p_3310_; uint8_t v___x_3311_; lean_object* v___x_3312_; lean_object* v_ictx_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_s_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3308_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3309_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3309_, 0, v_catName_3305_);
v_p_3310_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3310_, 0, v___x_3308_);
lean_closure_set(v_p_3310_, 1, v___x_3309_);
v___x_3311_ = 1;
v___x_3312_ = lean_string_utf8_byte_size(v_input_3306_);
lean_inc_ref(v_input_3306_);
v_ictx_3313_ = l_Lean_Parser_mkInputContext___redArg(v_input_3306_, v_fileName_3307_, v___x_3311_, v___x_3312_);
v___x_3314_ = l_Lean_Options_empty;
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_box(0);
lean_inc_ref(v_env_3304_);
v___x_3317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3317_, 0, v_env_3304_);
lean_ctor_set(v___x_3317_, 1, v___x_3314_);
lean_ctor_set(v___x_3317_, 2, v___x_3315_);
lean_ctor_set(v___x_3317_, 3, v___x_3316_);
v___x_3318_ = l_Lean_Parser_getTokenTable(v_env_3304_);
v___x_3319_ = l_Lean_Parser_mkParserState(v_input_3306_);
lean_dec_ref(v_input_3306_);
lean_inc_ref(v_ictx_3313_);
v_s_3320_ = l_Lean_Parser_ParserFn_run(v_p_3310_, v_ictx_3313_, v___x_3317_, v___x_3318_, v___x_3319_);
lean_inc_ref(v_s_3320_);
v___x_3321_ = l_Lean_Parser_ParserState_allErrors(v_s_3320_);
v___x_3322_ = lean_array_get_size(v___x_3321_);
lean_dec_ref(v___x_3321_);
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3324_ = lean_nat_dec_eq(v___x_3322_, v___x_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3313_, v_s_3320_);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
return v___x_3326_;
}
else
{
lean_object* v_stxStack_3327_; lean_object* v_pos_3328_; uint8_t v___x_3329_; 
v_stxStack_3327_ = lean_ctor_get(v_s_3320_, 0);
lean_inc_ref(v_stxStack_3327_);
v_pos_3328_ = lean_ctor_get(v_s_3320_, 2);
lean_inc(v_pos_3328_);
v___x_3329_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3313_, v_pos_3328_);
lean_dec(v_pos_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec_ref(v_stxStack_3327_);
v___x_3330_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3331_ = l_Lean_Parser_ParserState_mkError(v_s_3320_, v___x_3330_);
v___x_3332_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3313_, v___x_3331_);
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref(v_s_3320_);
lean_dec_ref(v_ictx_3313_);
v___x_3334_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3327_);
lean_dec_ref(v_stxStack_3327_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3336_, lean_object* v_catName_3337_, lean_object* v_declName_3338_, lean_object* v_prio_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v_val_3355_; lean_object* v___x_3356_; 
v___x_3343_ = lean_box(0);
v___x_3344_ = l_Lean_mkConst(v_addFnName_3336_, v___x_3343_);
v___x_3345_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3337_);
lean_inc_n(v_declName_3338_, 2);
v___x_3346_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3338_);
v___x_3347_ = l_Lean_mkConst(v_declName_3338_, v___x_3343_);
v___x_3348_ = l_Lean_mkRawNatLit(v_prio_3339_);
v___x_3349_ = lean_unsigned_to_nat(4u);
v___x_3350_ = lean_mk_empty_array_with_capacity(v___x_3349_);
v___x_3351_ = lean_array_push(v___x_3350_, v___x_3345_);
v___x_3352_ = lean_array_push(v___x_3351_, v___x_3346_);
v___x_3353_ = lean_array_push(v___x_3352_, v___x_3347_);
v___x_3354_ = lean_array_push(v___x_3353_, v___x_3348_);
v_val_3355_ = l_Lean_mkAppN(v___x_3344_, v___x_3354_);
lean_dec_ref(v___x_3354_);
v___x_3356_ = l_Lean_declareBuiltin(v_declName_3338_, v_val_3355_, v_a_3340_, v_a_3341_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3357_, lean_object* v_catName_3358_, lean_object* v_declName_3359_, lean_object* v_prio_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3357_, v_catName_3358_, v_declName_3359_, v_prio_3360_, v_a_3361_, v_a_3362_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3370_, lean_object* v_declName_3371_, lean_object* v_prio_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3377_ = l_Lean_Parser_declareBuiltinParser(v___x_3376_, v_catName_3370_, v_declName_3371_, v_prio_3372_, v_a_3373_, v_a_3374_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3378_, lean_object* v_declName_3379_, lean_object* v_prio_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3378_, v_declName_3379_, v_prio_3380_, v_a_3381_, v_a_3382_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3390_, lean_object* v_declName_3391_, lean_object* v_prio_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3397_ = l_Lean_Parser_declareBuiltinParser(v___x_3396_, v_catName_3390_, v_declName_3391_, v_prio_3392_, v_a_3393_, v_a_3394_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3398_, lean_object* v_declName_3399_, lean_object* v_prio_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3398_, v_declName_3399_, v_prio_3400_, v_a_3401_, v_a_3402_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3411_){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = l_Lean_Syntax_getNumArgs(v_args_3411_);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = lean_nat_dec_eq(v___x_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_3415_ = lean_unsigned_to_nat(1u);
v___x_3416_ = lean_nat_dec_eq(v___x_3412_, v___x_3415_);
lean_dec(v___x_3412_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3417_;
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = l_Lean_Syntax_getArg(v_args_3411_, v___x_3413_);
v___x_3419_ = l_Lean_Syntax_isNatLit_x3f(v___x_3418_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3420_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3421_ = l_Lean_Syntax_formatStx(v___x_3418_, v___x_3419_, v___x_3414_);
v___x_3422_ = l_Std_Format_defWidth;
v___x_3423_ = l_Std_Format_pretty(v___x_3421_, v___x_3422_, v___x_3413_, v___x_3413_);
v___x_3424_ = lean_string_append(v___x_3420_, v___x_3423_);
lean_dec_ref(v___x_3423_);
v___x_3425_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3426_ = lean_string_append(v___x_3424_, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
return v___x_3427_;
}
else
{
lean_object* v_val_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v___x_3418_);
v_val_3428_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3419_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_val_3428_);
lean_dec(v___x_3419_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_val_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
else
{
lean_object* v___x_3436_; 
lean_dec(v___x_3412_);
v___x_3436_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_Parser_getParserPriority(v_args_3437_);
lean_dec(v_args_3437_);
return v_res_3438_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3441_ = l_Lean_stringToMessageData(v___x_3440_);
return v___x_3441_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3444_ = l_Lean_stringToMessageData(v___x_3443_);
return v___x_3444_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3446_ = l_Lean_stringToMessageData(v___x_3445_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3450_, uint8_t v_kind_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___y_3461_; 
v___x_3455_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3456_ = l_Lean_MessageData_ofName(v_name_3450_);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
switch(v_kind_3451_)
{
case 0:
{
lean_object* v___x_3468_; 
v___x_3468_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3461_ = v___x_3468_;
goto v___jp_3460_;
}
case 1:
{
lean_object* v___x_3469_; 
v___x_3469_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3461_ = v___x_3469_;
goto v___jp_3460_;
}
default: 
{
lean_object* v___x_3470_; 
v___x_3470_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3461_ = v___x_3470_;
goto v___jp_3460_;
}
}
v___jp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_inc_ref(v___y_3461_);
v___x_3462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___y_3461_);
v___x_3463_ = l_Lean_MessageData_ofFormat(v___x_3462_);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3459_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3466_, v___y_3452_, v___y_3453_);
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3471_, lean_object* v_kind_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
uint8_t v_kind_boxed_3476_; lean_object* v_res_3477_; 
v_kind_boxed_3476_ = lean_unbox(v_kind_3472_);
v_res_3477_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3471_, v_kind_boxed_3476_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3478_, lean_object* v_msg_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_fileName_3483_; lean_object* v_fileMap_3484_; lean_object* v_options_3485_; lean_object* v_currRecDepth_3486_; lean_object* v_maxRecDepth_3487_; lean_object* v_ref_3488_; lean_object* v_currNamespace_3489_; lean_object* v_openDecls_3490_; lean_object* v_initHeartbeats_3491_; lean_object* v_maxHeartbeats_3492_; lean_object* v_quotContext_3493_; lean_object* v_currMacroScope_3494_; uint8_t v_diag_3495_; lean_object* v_cancelTk_x3f_3496_; uint8_t v_suppressElabErrors_3497_; lean_object* v_inheritedTraceOptions_3498_; lean_object* v_ref_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v_fileName_3483_ = lean_ctor_get(v___y_3480_, 0);
v_fileMap_3484_ = lean_ctor_get(v___y_3480_, 1);
v_options_3485_ = lean_ctor_get(v___y_3480_, 2);
v_currRecDepth_3486_ = lean_ctor_get(v___y_3480_, 3);
v_maxRecDepth_3487_ = lean_ctor_get(v___y_3480_, 4);
v_ref_3488_ = lean_ctor_get(v___y_3480_, 5);
v_currNamespace_3489_ = lean_ctor_get(v___y_3480_, 6);
v_openDecls_3490_ = lean_ctor_get(v___y_3480_, 7);
v_initHeartbeats_3491_ = lean_ctor_get(v___y_3480_, 8);
v_maxHeartbeats_3492_ = lean_ctor_get(v___y_3480_, 9);
v_quotContext_3493_ = lean_ctor_get(v___y_3480_, 10);
v_currMacroScope_3494_ = lean_ctor_get(v___y_3480_, 11);
v_diag_3495_ = lean_ctor_get_uint8(v___y_3480_, sizeof(void*)*14);
v_cancelTk_x3f_3496_ = lean_ctor_get(v___y_3480_, 12);
v_suppressElabErrors_3497_ = lean_ctor_get_uint8(v___y_3480_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3498_ = lean_ctor_get(v___y_3480_, 13);
v_ref_3499_ = l_Lean_replaceRef(v_ref_3478_, v_ref_3488_);
lean_inc_ref(v_inheritedTraceOptions_3498_);
lean_inc(v_cancelTk_x3f_3496_);
lean_inc(v_currMacroScope_3494_);
lean_inc(v_quotContext_3493_);
lean_inc(v_maxHeartbeats_3492_);
lean_inc(v_initHeartbeats_3491_);
lean_inc(v_openDecls_3490_);
lean_inc(v_currNamespace_3489_);
lean_inc(v_maxRecDepth_3487_);
lean_inc(v_currRecDepth_3486_);
lean_inc_ref(v_options_3485_);
lean_inc_ref(v_fileMap_3484_);
lean_inc_ref(v_fileName_3483_);
v___x_3500_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3500_, 0, v_fileName_3483_);
lean_ctor_set(v___x_3500_, 1, v_fileMap_3484_);
lean_ctor_set(v___x_3500_, 2, v_options_3485_);
lean_ctor_set(v___x_3500_, 3, v_currRecDepth_3486_);
lean_ctor_set(v___x_3500_, 4, v_maxRecDepth_3487_);
lean_ctor_set(v___x_3500_, 5, v_ref_3499_);
lean_ctor_set(v___x_3500_, 6, v_currNamespace_3489_);
lean_ctor_set(v___x_3500_, 7, v_openDecls_3490_);
lean_ctor_set(v___x_3500_, 8, v_initHeartbeats_3491_);
lean_ctor_set(v___x_3500_, 9, v_maxHeartbeats_3492_);
lean_ctor_set(v___x_3500_, 10, v_quotContext_3493_);
lean_ctor_set(v___x_3500_, 11, v_currMacroScope_3494_);
lean_ctor_set(v___x_3500_, 12, v_cancelTk_x3f_3496_);
lean_ctor_set(v___x_3500_, 13, v_inheritedTraceOptions_3498_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*14, v_diag_3495_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*14 + 1, v_suppressElabErrors_3497_);
v___x_3501_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3479_, v___x_3500_, v___y_3481_);
lean_dec_ref_known(v___x_3500_, 14);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3502_, lean_object* v_msg_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3502_, v_msg_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v_ref_3502_);
return v_res_3507_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3510_ = l_Lean_stringToMessageData(v___x_3509_);
return v___x_3510_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3513_ = l_Lean_stringToMessageData(v___x_3512_);
return v___x_3513_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3516_ = l_Lean_stringToMessageData(v___x_3515_);
return v___x_3516_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3519_ = l_Lean_stringToMessageData(v___x_3518_);
return v___x_3519_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
return v___x_3522_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3525_ = l_Lean_stringToMessageData(v___x_3524_);
return v___x_3525_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3528_ = l_Lean_stringToMessageData(v___x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3529_, lean_object* v_declHint_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3533_; lean_object* v_env_3534_; uint8_t v___x_3535_; 
v___x_3533_ = lean_st_ref_get(v___y_3531_);
v_env_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc_ref(v_env_3534_);
lean_dec(v___x_3533_);
v___x_3535_ = l_Lean_Name_isAnonymous(v_declHint_3530_);
if (v___x_3535_ == 0)
{
uint8_t v_isExporting_3536_; 
v_isExporting_3536_ = lean_ctor_get_uint8(v_env_3534_, sizeof(void*)*8);
if (v_isExporting_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_dec_ref(v_env_3534_);
lean_dec(v_declHint_3530_);
v___x_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3537_, 0, v_msg_3529_);
return v___x_3537_;
}
else
{
lean_object* v___x_3538_; uint8_t v___x_3539_; 
lean_inc_ref(v_env_3534_);
v___x_3538_ = l_Lean_Environment_setExporting(v_env_3534_, v___x_3535_);
lean_inc(v_declHint_3530_);
lean_inc_ref(v___x_3538_);
v___x_3539_ = l_Lean_Environment_contains(v___x_3538_, v_declHint_3530_, v_isExporting_3536_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref(v___x_3538_);
lean_dec_ref(v_env_3534_);
lean_dec(v_declHint_3530_);
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v_msg_3529_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v_c_3546_; lean_object* v___x_3547_; 
v___x_3541_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_3542_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_3543_ = l_Lean_Options_empty;
v___x_3544_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3538_);
lean_ctor_set(v___x_3544_, 1, v___x_3541_);
lean_ctor_set(v___x_3544_, 2, v___x_3542_);
lean_ctor_set(v___x_3544_, 3, v___x_3543_);
lean_inc(v_declHint_3530_);
v___x_3545_ = l_Lean_MessageData_ofConstName(v_declHint_3530_, v___x_3535_);
v_c_3546_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3546_, 0, v___x_3544_);
lean_ctor_set(v_c_3546_, 1, v___x_3545_);
v___x_3547_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3534_, v_declHint_3530_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec_ref(v_env_3534_);
lean_dec(v_declHint_3530_);
v___x_3548_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v_c_3546_);
v___x_3550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = l_Lean_MessageData_note(v___x_3551_);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v_msg_3529_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
else
{
lean_object* v_val_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3590_; 
v_val_3555_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3557_ = v___x_3547_;
v_isShared_3558_ = v_isSharedCheck_3590_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_val_3555_);
lean_dec(v___x_3547_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3590_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v_mod_3562_; uint8_t v___x_3563_; 
v___x_3559_ = lean_box(0);
v___x_3560_ = l_Lean_Environment_header(v_env_3534_);
lean_dec_ref(v_env_3534_);
v___x_3561_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3560_);
v_mod_3562_ = lean_array_get(v___x_3559_, v___x_3561_, v_val_3555_);
lean_dec(v_val_3555_);
lean_dec_ref(v___x_3561_);
v___x_3563_ = l_Lean_isPrivateName(v_declHint_3530_);
lean_dec(v_declHint_3530_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
lean_ctor_set(v___x_3565_, 1, v_c_3546_);
v___x_3566_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3565_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = l_Lean_MessageData_ofName(v_mod_3562_);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3569_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = l_Lean_MessageData_note(v___x_3571_);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v_msg_3529_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3573_);
v___x_3575_ = v___x_3557_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3577_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v_c_3546_);
v___x_3579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = l_Lean_MessageData_ofName(v_mod_3562_);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = l_Lean_MessageData_note(v___x_3584_);
v___x_3586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3586_, 0, v_msg_3529_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3586_);
v___x_3588_ = v___x_3557_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3591_; 
lean_dec_ref(v_env_3534_);
lean_dec(v_declHint_3530_);
v___x_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3591_, 0, v_msg_3529_);
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3592_, lean_object* v_declHint_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3592_, v_declHint_3593_, v___y_3594_);
lean_dec(v___y_3594_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3597_, lean_object* v_declHint_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3612_; 
v___x_3602_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3597_, v_declHint_3598_, v___y_3600_);
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3607_ = l_Lean_unknownIdentifierMessageTag;
v___x_3608_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v_a_3603_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3608_);
v___x_3610_ = v___x_3605_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3613_, lean_object* v_declHint_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3613_, v_declHint_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3619_, lean_object* v_msg_3620_, lean_object* v_declHint_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; lean_object* v_a_3626_; lean_object* v___x_3627_; 
v___x_3625_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3620_, v_declHint_3621_, v___y_3622_, v___y_3623_);
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref(v___x_3625_);
v___x_3627_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3619_, v_a_3626_, v___y_3622_, v___y_3623_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3628_, lean_object* v_msg_3629_, lean_object* v_declHint_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3628_, v_msg_3629_, v_declHint_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v_ref_3628_);
return v_res_3634_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3636_ = l_Lean_stringToMessageData(v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3637_, lean_object* v_constName_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3642_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3643_ = 0;
lean_inc(v_constName_3638_);
v___x_3644_ = l_Lean_MessageData_ofConstName(v_constName_3638_, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3642_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3637_, v___x_3647_, v_constName_3638_, v___y_3639_, v___y_3640_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3649_, lean_object* v_constName_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3649_, v_constName_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_ref_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_ref_3659_; lean_object* v___x_3660_; 
v_ref_3659_ = lean_ctor_get(v___y_3656_, 5);
v___x_3660_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3659_, v_constName_3655_, v___y_3656_, v___y_3657_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3661_, v___y_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v___x_3670_; lean_object* v_env_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; 
v___x_3670_ = lean_st_ref_get(v___y_3668_);
v_env_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc_ref(v_env_3671_);
lean_dec(v___x_3670_);
v___x_3672_ = 0;
lean_inc(v_constName_3666_);
v___x_3673_ = l_Lean_Environment_find_x3f(v_env_3671_, v_constName_3666_, v___x_3672_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3666_, v___y_3667_, v___y_3668_);
return v___x_3674_;
}
else
{
lean_object* v_val_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v_constName_3666_);
v_val_3675_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3673_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_val_3675_);
lean_dec(v___x_3673_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set_tag(v___x_3677_, 0);
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_val_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3687_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3690_ = l_Lean_stringToMessageData(v___x_3689_);
return v___x_3690_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3693_ = l_Lean_stringToMessageData(v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3694_, lean_object* v_catName_3695_, lean_object* v_declName_3696_, lean_object* v_stx_3697_, uint8_t v_kind_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3697_, v_a_3699_, v_a_3700_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___y_3725_; lean_object* v___y_3726_; uint8_t v___x_3754_; uint8_t v___x_3755_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v___x_3754_ = 0;
v___x_3755_ = l_Lean_instBEqAttributeKind_beq(v_kind_3698_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; 
lean_dec(v_a_3723_);
lean_dec(v_declName_3696_);
lean_dec(v_catName_3695_);
v___x_3756_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3694_, v_kind_3698_, v_a_3699_, v_a_3700_);
return v___x_3756_;
}
else
{
lean_dec(v_attrName_3694_);
v___y_3725_ = v_a_3699_;
v___y_3726_ = v_a_3700_;
goto v___jp_3724_;
}
v___jp_3724_:
{
lean_object* v___x_3727_; 
lean_inc(v_declName_3696_);
v___x_3727_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3696_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = l_Lean_ConstantInfo_type(v_a_3728_);
if (lean_obj_tag(v___x_3729_) == 4)
{
lean_object* v_declName_3730_; 
v_declName_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_declName_3730_);
lean_dec_ref_known(v___x_3729_, 2);
if (lean_obj_tag(v_declName_3730_) == 1)
{
lean_object* v_pre_3731_; 
v_pre_3731_ = lean_ctor_get(v_declName_3730_, 0);
lean_inc(v_pre_3731_);
if (lean_obj_tag(v_pre_3731_) == 1)
{
lean_object* v_pre_3732_; 
v_pre_3732_ = lean_ctor_get(v_pre_3731_, 0);
lean_inc(v_pre_3732_);
if (lean_obj_tag(v_pre_3732_) == 1)
{
lean_object* v_pre_3733_; 
v_pre_3733_ = lean_ctor_get(v_pre_3732_, 0);
if (lean_obj_tag(v_pre_3733_) == 0)
{
lean_object* v_str_3734_; lean_object* v_str_3735_; lean_object* v_str_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; 
v_str_3734_ = lean_ctor_get(v_declName_3730_, 1);
lean_inc_ref(v_str_3734_);
lean_dec_ref_known(v_declName_3730_, 2);
v_str_3735_ = lean_ctor_get(v_pre_3731_, 1);
lean_inc_ref(v_str_3735_);
lean_dec_ref_known(v_pre_3731_, 2);
v_str_3736_ = lean_ctor_get(v_pre_3732_, 1);
lean_inc_ref(v_str_3736_);
lean_dec_ref_known(v_pre_3732_, 2);
v___x_3737_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3738_ = lean_string_dec_eq(v_str_3736_, v___x_3737_);
lean_dec_ref(v_str_3736_);
if (v___x_3738_ == 0)
{
lean_dec_ref(v_str_3735_);
lean_dec_ref(v_str_3734_);
lean_dec(v_a_3723_);
lean_dec(v_catName_3695_);
v___y_3709_ = v_a_3728_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3739_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3740_ = lean_string_dec_eq(v_str_3735_, v___x_3739_);
lean_dec_ref(v_str_3735_);
if (v___x_3740_ == 0)
{
lean_dec_ref(v_str_3734_);
lean_dec(v_a_3723_);
lean_dec(v_catName_3695_);
v___y_3709_ = v_a_3728_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3741_; uint8_t v___x_3742_; 
v___x_3741_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3742_ = lean_string_dec_eq(v_str_3734_, v___x_3741_);
if (v___x_3742_ == 0)
{
uint8_t v___x_3743_; 
v___x_3743_ = lean_string_dec_eq(v_str_3734_, v___x_3739_);
lean_dec_ref(v_str_3734_);
if (v___x_3743_ == 0)
{
lean_dec(v_a_3723_);
lean_dec(v_catName_3695_);
v___y_3709_ = v_a_3728_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3744_; 
lean_dec(v_a_3728_);
lean_inc(v_declName_3696_);
lean_inc(v_catName_3695_);
v___x_3744_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3695_, v_declName_3696_, v_a_3723_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_dec_ref_known(v___x_3744_, 1);
v___y_3703_ = v___y_3725_;
v___y_3704_ = v___y_3726_;
goto v___jp_3702_;
}
else
{
lean_dec(v_declName_3696_);
lean_dec(v_catName_3695_);
return v___x_3744_;
}
}
}
else
{
lean_object* v___x_3745_; 
lean_dec_ref(v_str_3734_);
lean_dec(v_a_3728_);
lean_inc(v_declName_3696_);
lean_inc(v_catName_3695_);
v___x_3745_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3695_, v_declName_3696_, v_a_3723_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_dec_ref_known(v___x_3745_, 1);
v___y_3703_ = v___y_3725_;
v___y_3704_ = v___y_3726_;
goto v___jp_3702_;
}
else
{
lean_dec(v_declName_3696_);
lean_dec(v_catName_3695_);
return v___x_3745_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3732_, 2);
lean_dec_ref_known(v_pre_3731_, 2);
lean_dec_ref_known(v_declName_3730_, 2);
lean_dec(v_a_3723_);
lean_dec(v_catName_3695_);
v___y_3709_ = v_a_3728_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
goto v___jp_3708_;
}
}
else
{
lean_dec(v_pre_3732_);
lean_dec_ref_known(v_pre_3731_, 2);
lean_dec_ref_known(v_declName_3730_, 2);
lean_dec(v_a_3723_);
lean_dec(v_catName_3695_);
v___y_3709_ = v_a_3728_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
goto v___jp_3708_;
}
}
else
{
lean_dec_ref_known(v_declName_3730_, 2);
lean_dec(v_pre_3731_);
lean_dec(v_a_3723_);
lean_dec(v_catName_3695_);
v___y_3709_ = v_a_3728_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
goto v___jp_3708_;
}
}
else
{
lean_dec(v_declName_3730_);
lean_dec(v_a_3723_);
lean_dec(v_catName_3695_);
v___y_3709_ = v_a_3728_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
goto v___jp_3708_;
}
}
else
{
lean_dec_ref(v___x_3729_);
lean_dec(v_a_3723_);
lean_dec(v_catName_3695_);
v___y_3709_ = v_a_3728_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
goto v___jp_3708_;
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_a_3723_);
lean_dec(v_declName_3696_);
lean_dec(v_catName_3695_);
v_a_3746_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3727_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3727_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_declName_3696_);
lean_dec(v_catName_3695_);
lean_dec(v_attrName_3694_);
v_a_3757_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3722_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3722_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
v___jp_3702_:
{
lean_object* v___x_3705_; 
lean_inc(v_declName_3696_);
v___x_3705_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3696_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3705_) == 0)
{
uint8_t v___x_3706_; lean_object* v___x_3707_; 
lean_dec_ref_known(v___x_3705_, 1);
v___x_3706_ = 1;
v___x_3707_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3695_, v_declName_3696_, v___x_3706_, v___y_3703_, v___y_3704_);
return v___x_3707_;
}
else
{
lean_dec(v_declName_3696_);
lean_dec(v_catName_3695_);
return v___x_3705_;
}
}
v___jp_3708_:
{
lean_object* v___x_3712_; uint8_t v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3712_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3713_ = 0;
v___x_3714_ = l_Lean_MessageData_ofConstName(v_declName_3696_, v___x_3713_);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3712_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = l_Lean_ConstantInfo_type(v___y_3709_);
lean_dec_ref(v___y_3709_);
v___x_3719_ = l_Lean_indentExpr(v___x_3718_);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3717_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3720_, v___y_3710_, v___y_3711_);
return v___x_3721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3765_, lean_object* v_catName_3766_, lean_object* v_declName_3767_, lean_object* v_stx_3768_, lean_object* v_kind_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_){
_start:
{
uint8_t v_kind_boxed_3773_; lean_object* v_res_3774_; 
v_kind_boxed_3773_ = lean_unbox(v_kind_3769_);
v_res_3774_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3765_, v_catName_3766_, v_declName_3767_, v_stx_3768_, v_kind_boxed_3773_, v_a_3770_, v_a_3771_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3775_, lean_object* v_name_3776_, uint8_t v_kind_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3776_, v_kind_3777_, v___y_3778_, v___y_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3782_, lean_object* v_name_3783_, lean_object* v_kind_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
uint8_t v_kind_boxed_3788_; lean_object* v_res_3789_; 
v_kind_boxed_3788_ = lean_unbox(v_kind_3784_);
v_res_3789_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3782_, v_name_3783_, v_kind_boxed_3788_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3790_, lean_object* v_constName_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3791_, v___y_3792_, v___y_3793_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3796_, lean_object* v_constName_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3796_, v_constName_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3802_, lean_object* v_ref_3803_, lean_object* v_constName_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3803_, v_constName_3804_, v___y_3805_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3809_, lean_object* v_ref_3810_, lean_object* v_constName_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3809_, v_ref_3810_, v_constName_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v_ref_3810_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3816_, lean_object* v_ref_3817_, lean_object* v_msg_3818_, lean_object* v_declHint_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3817_, v_msg_3818_, v_declHint_3819_, v___y_3820_, v___y_3821_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3824_, lean_object* v_ref_3825_, lean_object* v_msg_3826_, lean_object* v_declHint_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3824_, v_ref_3825_, v_msg_3826_, v_declHint_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v_ref_3825_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3832_, lean_object* v_declHint_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3832_, v_declHint_3833_, v___y_3835_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3838_, lean_object* v_declHint_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3838_, v_declHint_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3844_, lean_object* v_ref_3845_, lean_object* v_msg_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3845_, v_msg_3846_, v___y_3847_, v___y_3848_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3851_, lean_object* v_ref_3852_, lean_object* v_msg_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3851_, v_ref_3852_, v_msg_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v_ref_3852_);
return v_res_3857_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3865_ = l_Lean_mkAtom(v___x_3864_);
return v___x_3865_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3867_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3868_ = lean_array_push(v___x_3867_, v___x_3866_);
return v___x_3868_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3878_ = l_Lean_mkAtom(v___x_3877_);
return v___x_3878_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3880_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3881_ = lean_array_push(v___x_3880_, v___x_3879_);
return v___x_3881_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3882_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3883_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3884_ = lean_box(2);
v___x_3885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
lean_ctor_set(v___x_3885_, 1, v___x_3883_);
lean_ctor_set(v___x_3885_, 2, v___x_3882_);
return v___x_3885_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3887_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3888_ = lean_array_push(v___x_3887_, v___x_3886_);
return v___x_3888_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3889_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3890_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3891_ = lean_box(2);
v___x_3892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
lean_ctor_set(v___x_3892_, 1, v___x_3890_);
lean_ctor_set(v___x_3892_, 2, v___x_3889_);
return v___x_3892_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3894_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3895_ = lean_array_push(v___x_3894_, v___x_3893_);
return v___x_3895_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3896_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3897_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3898_ = lean_box(2);
v___x_3899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
lean_ctor_set(v___x_3899_, 1, v___x_3897_);
lean_ctor_set(v___x_3899_, 2, v___x_3896_);
return v___x_3899_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3900_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3901_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3902_ = lean_array_push(v___x_3901_, v___x_3900_);
return v___x_3902_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3903_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3904_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3905_ = lean_box(2);
v___x_3906_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v___x_3904_);
lean_ctor_set(v___x_3906_, 2, v___x_3903_);
return v___x_3906_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3908_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3909_ = lean_array_push(v___x_3908_, v___x_3907_);
return v___x_3909_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3910_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3911_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3912_ = lean_box(2);
v___x_3913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v___x_3911_);
lean_ctor_set(v___x_3913_, 2, v___x_3910_);
return v___x_3913_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3915_, lean_object* v_decl_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3920_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3921_ = l_Lean_MessageData_ofName(v_attrName_3915_);
v___x_3922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3920_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
v___x_3923_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3922_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3924_, v___y_3917_, v___y_3918_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3926_, lean_object* v_decl_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3926_, v_decl_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v_decl_3927_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3932_, lean_object* v_catName_3933_, lean_object* v_declName_3934_, lean_object* v_stx_3935_, uint8_t v_kind_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3932_, v_catName_3933_, v_declName_3934_, v_stx_3935_, v_kind_3936_, v___y_3937_, v___y_3938_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3941_, lean_object* v_catName_3942_, lean_object* v_declName_3943_, lean_object* v_stx_3944_, lean_object* v_kind_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v_kind_boxed_3949_; lean_object* v_res_3950_; 
v_kind_boxed_3949_ = lean_unbox(v_kind_3945_);
v_res_3950_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3941_, v_catName_3942_, v_declName_3943_, v_stx_3944_, v_kind_boxed_3949_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3950_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3952_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3953_ = lean_mk_io_user_error(v___x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3956_, lean_object* v_declName_3957_, uint8_t v_behavior_3958_, lean_object* v_ref_3959_){
_start:
{
if (lean_obj_tag(v_declName_3957_) == 1)
{
lean_object* v_pre_3964_; 
v_pre_3964_ = lean_ctor_get(v_declName_3957_, 0);
if (lean_obj_tag(v_pre_3964_) == 1)
{
lean_object* v_pre_3965_; 
v_pre_3965_ = lean_ctor_get(v_pre_3964_, 0);
if (lean_obj_tag(v_pre_3965_) == 1)
{
lean_object* v_pre_3966_; 
v_pre_3966_ = lean_ctor_get(v_pre_3965_, 0);
if (lean_obj_tag(v_pre_3966_) == 1)
{
lean_object* v_pre_3967_; 
v_pre_3967_ = lean_ctor_get(v_pre_3966_, 0);
if (lean_obj_tag(v_pre_3967_) == 0)
{
lean_object* v_str_3968_; lean_object* v_str_3969_; lean_object* v_str_3970_; lean_object* v_str_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v_str_3968_ = lean_ctor_get(v_declName_3957_, 1);
v_str_3969_ = lean_ctor_get(v_pre_3964_, 1);
v_str_3970_ = lean_ctor_get(v_pre_3965_, 1);
v_str_3971_ = lean_ctor_get(v_pre_3966_, 1);
v___x_3972_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3973_ = lean_string_dec_eq(v_str_3971_, v___x_3972_);
if (v___x_3973_ == 0)
{
lean_dec_ref_known(v_declName_3957_, 2);
lean_dec(v_ref_3959_);
lean_dec(v_attrName_3956_);
goto v___jp_3961_;
}
else
{
lean_object* v___x_3974_; uint8_t v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3975_ = lean_string_dec_eq(v_str_3970_, v___x_3974_);
if (v___x_3975_ == 0)
{
lean_dec_ref_known(v_declName_3957_, 2);
lean_dec(v_ref_3959_);
lean_dec(v_attrName_3956_);
goto v___jp_3961_;
}
else
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3976_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3977_ = lean_string_dec_eq(v_str_3969_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_dec_ref_known(v_declName_3957_, 2);
lean_dec(v_ref_3959_);
lean_dec(v_attrName_3956_);
goto v___jp_3961_;
}
else
{
lean_object* v___x_3978_; lean_object* v_catName_3979_; lean_object* v___x_3980_; 
v___x_3978_ = lean_box(0);
lean_inc_ref(v_str_3968_);
v_catName_3979_ = l_Lean_Name_str___override(v___x_3978_, v_str_3968_);
lean_inc(v_catName_3979_);
v___x_3980_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3979_, v_declName_3957_, v_behavior_3958_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v___f_3981_; lean_object* v___f_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
lean_dec_ref_known(v___x_3980_, 1);
lean_inc_n(v_attrName_3956_, 2);
v___f_3981_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3981_, 0, v_attrName_3956_);
v___f_3982_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3982_, 0, v_attrName_3956_);
lean_closure_set(v___f_3982_, 1, v_catName_3979_);
v___x_3983_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_3984_ = 1;
v___x_3985_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3985_, 0, v_ref_3959_);
lean_ctor_set(v___x_3985_, 1, v_attrName_3956_);
lean_ctor_set(v___x_3985_, 2, v___x_3983_);
lean_ctor_set_uint8(v___x_3985_, sizeof(void*)*3, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
lean_ctor_set(v___x_3986_, 1, v___f_3982_);
lean_ctor_set(v___x_3986_, 2, v___f_3981_);
v___x_3987_ = l_Lean_registerBuiltinAttribute(v___x_3986_);
return v___x_3987_;
}
else
{
lean_dec(v_catName_3979_);
lean_dec(v_ref_3959_);
lean_dec(v_attrName_3956_);
return v___x_3980_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_3957_, 2);
lean_dec(v_ref_3959_);
lean_dec(v_attrName_3956_);
goto v___jp_3961_;
}
}
else
{
lean_dec_ref_known(v_declName_3957_, 2);
lean_dec(v_ref_3959_);
lean_dec(v_attrName_3956_);
goto v___jp_3961_;
}
}
else
{
lean_dec_ref_known(v_declName_3957_, 2);
lean_dec(v_ref_3959_);
lean_dec(v_attrName_3956_);
goto v___jp_3961_;
}
}
else
{
lean_dec_ref_known(v_declName_3957_, 2);
lean_dec(v_ref_3959_);
lean_dec(v_attrName_3956_);
goto v___jp_3961_;
}
}
else
{
lean_dec(v_ref_3959_);
lean_dec(v_declName_3957_);
lean_dec(v_attrName_3956_);
goto v___jp_3961_;
}
v___jp_3961_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_3988_, lean_object* v_declName_3989_, lean_object* v_behavior_3990_, lean_object* v_ref_3991_, lean_object* v_a_3992_){
_start:
{
uint8_t v_behavior_boxed_3993_; lean_object* v_res_3994_; 
v_behavior_boxed_3993_ = lean_unbox(v_behavior_3990_);
v_res_3994_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_3988_, v_declName_3989_, v_behavior_boxed_3993_, v_ref_3991_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_3995_, lean_object* v_x_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v___x_4000_; lean_object* v_env_4001_; lean_object* v_nextMacroScope_4002_; lean_object* v_ngen_4003_; lean_object* v_auxDeclNGen_4004_; lean_object* v_traceState_4005_; lean_object* v_messages_4006_; lean_object* v_infoState_4007_; lean_object* v_snapshotTasks_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4020_; 
v___x_4000_ = lean_st_ref_take(v___y_3998_);
v_env_4001_ = lean_ctor_get(v___x_4000_, 0);
v_nextMacroScope_4002_ = lean_ctor_get(v___x_4000_, 1);
v_ngen_4003_ = lean_ctor_get(v___x_4000_, 2);
v_auxDeclNGen_4004_ = lean_ctor_get(v___x_4000_, 3);
v_traceState_4005_ = lean_ctor_get(v___x_4000_, 4);
v_messages_4006_ = lean_ctor_get(v___x_4000_, 6);
v_infoState_4007_ = lean_ctor_get(v___x_4000_, 7);
v_snapshotTasks_4008_ = lean_ctor_get(v___x_4000_, 8);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4020_ == 0)
{
lean_object* v_unused_4021_; 
v_unused_4021_ = lean_ctor_get(v___x_4000_, 5);
lean_dec(v_unused_4021_);
v___x_4010_ = v___x_4000_;
v_isShared_4011_ = v_isSharedCheck_4020_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_snapshotTasks_4008_);
lean_inc(v_infoState_4007_);
lean_inc(v_messages_4006_);
lean_inc(v_traceState_4005_);
lean_inc(v_auxDeclNGen_4004_);
lean_inc(v_ngen_4003_);
lean_inc(v_nextMacroScope_4002_);
lean_inc(v_env_4001_);
lean_dec(v___x_4000_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4020_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4012_ = l_Lean_Parser_addSyntaxNodeKind(v_env_4001_, v_kind_3995_);
v___x_4013_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 5, v___x_4013_);
lean_ctor_set(v___x_4010_, 0, v___x_4012_);
v___x_4015_ = v___x_4010_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v_nextMacroScope_4002_);
lean_ctor_set(v_reuseFailAlloc_4019_, 2, v_ngen_4003_);
lean_ctor_set(v_reuseFailAlloc_4019_, 3, v_auxDeclNGen_4004_);
lean_ctor_set(v_reuseFailAlloc_4019_, 4, v_traceState_4005_);
lean_ctor_set(v_reuseFailAlloc_4019_, 5, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4019_, 6, v_messages_4006_);
lean_ctor_set(v_reuseFailAlloc_4019_, 7, v_infoState_4007_);
lean_ctor_set(v_reuseFailAlloc_4019_, 8, v_snapshotTasks_4008_);
v___x_4015_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = lean_st_ref_put(v___y_3998_, v___x_4015_);
v___x_4017_ = lean_box(0);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4022_, lean_object* v_x_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4022_, v_x_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4028_, lean_object* v_keys_4029_, lean_object* v_vals_4030_, lean_object* v_i_4031_, lean_object* v_acc_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v___x_4036_; uint8_t v___x_4037_; 
v___x_4036_ = lean_array_get_size(v_keys_4029_);
v___x_4037_ = lean_nat_dec_lt(v_i_4031_, v___x_4036_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; 
lean_dec(v_i_4031_);
lean_dec_ref(v_f_4028_);
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v_acc_4032_);
return v___x_4038_;
}
else
{
lean_object* v_k_4039_; lean_object* v_v_4040_; lean_object* v___x_4041_; 
v_k_4039_ = lean_array_fget_borrowed(v_keys_4029_, v_i_4031_);
v_v_4040_ = lean_array_fget_borrowed(v_vals_4030_, v_i_4031_);
lean_inc_ref(v_f_4028_);
lean_inc(v___y_4034_);
lean_inc_ref(v___y_4033_);
lean_inc(v_v_4040_);
lean_inc(v_k_4039_);
v___x_4041_ = lean_apply_6(v_f_4028_, v_acc_4032_, v_k_4039_, v_v_4040_, v___y_4033_, v___y_4034_, lean_box(0));
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___x_4041_, 1);
v___x_4043_ = lean_unsigned_to_nat(1u);
v___x_4044_ = lean_nat_add(v_i_4031_, v___x_4043_);
lean_dec(v_i_4031_);
v_i_4031_ = v___x_4044_;
v_acc_4032_ = v_a_4042_;
goto _start;
}
else
{
lean_dec(v_i_4031_);
lean_dec_ref(v_f_4028_);
return v___x_4041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4046_, lean_object* v_keys_4047_, lean_object* v_vals_4048_, lean_object* v_i_4049_, lean_object* v_acc_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4046_, v_keys_4047_, v_vals_4048_, v_i_4049_, v_acc_4050_, v___y_4051_, v___y_4052_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec_ref(v_vals_4048_);
lean_dec_ref(v_keys_4047_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4055_, lean_object* v_x_4056_, lean_object* v_x_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
if (lean_obj_tag(v_x_4056_) == 0)
{
lean_object* v_es_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4081_; 
v_es_4061_ = lean_ctor_get(v_x_4056_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_x_4056_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4063_ = v_x_4056_;
v_isShared_4064_ = v_isSharedCheck_4081_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_es_4061_);
lean_dec(v_x_4056_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4081_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; 
v___x_4065_ = lean_unsigned_to_nat(0u);
v___x_4066_ = lean_array_get_size(v_es_4061_);
v___x_4067_ = lean_nat_dec_lt(v___x_4065_, v___x_4066_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4069_; 
lean_dec_ref(v_es_4061_);
lean_dec_ref(v_f_4055_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v_x_4057_);
v___x_4069_ = v___x_4063_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_x_4057_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
else
{
uint8_t v___x_4071_; 
v___x_4071_ = lean_nat_dec_le(v___x_4066_, v___x_4066_);
if (v___x_4071_ == 0)
{
if (v___x_4067_ == 0)
{
lean_object* v___x_4073_; 
lean_dec_ref(v_es_4061_);
lean_dec_ref(v_f_4055_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v_x_4057_);
v___x_4073_ = v___x_4063_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_x_4057_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
else
{
size_t v___x_4075_; size_t v___x_4076_; lean_object* v___x_4077_; 
lean_del_object(v___x_4063_);
v___x_4075_ = ((size_t)0ULL);
v___x_4076_ = lean_usize_of_nat(v___x_4066_);
v___x_4077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4055_, v_es_4061_, v___x_4075_, v___x_4076_, v_x_4057_, v___y_4058_, v___y_4059_);
lean_dec_ref(v_es_4061_);
return v___x_4077_;
}
}
else
{
size_t v___x_4078_; size_t v___x_4079_; lean_object* v___x_4080_; 
lean_del_object(v___x_4063_);
v___x_4078_ = ((size_t)0ULL);
v___x_4079_ = lean_usize_of_nat(v___x_4066_);
v___x_4080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4055_, v_es_4061_, v___x_4078_, v___x_4079_, v_x_4057_, v___y_4058_, v___y_4059_);
lean_dec_ref(v_es_4061_);
return v___x_4080_;
}
}
}
}
else
{
lean_object* v_ks_4082_; lean_object* v_vs_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v_ks_4082_ = lean_ctor_get(v_x_4056_, 0);
lean_inc_ref(v_ks_4082_);
v_vs_4083_ = lean_ctor_get(v_x_4056_, 1);
lean_inc_ref(v_vs_4083_);
lean_dec_ref_known(v_x_4056_, 2);
v___x_4084_ = lean_unsigned_to_nat(0u);
v___x_4085_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4055_, v_ks_4082_, v_vs_4083_, v___x_4084_, v_x_4057_, v___y_4058_, v___y_4059_);
lean_dec_ref(v_vs_4083_);
lean_dec_ref(v_ks_4082_);
return v___x_4085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4086_, lean_object* v_as_4087_, size_t v_i_4088_, size_t v_stop_4089_, lean_object* v_b_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_a_4095_; lean_object* v___y_4100_; uint8_t v___x_4102_; 
v___x_4102_ = lean_usize_dec_eq(v_i_4088_, v_stop_4089_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_array_uget_borrowed(v_as_4087_, v_i_4088_);
switch(lean_obj_tag(v___x_4103_))
{
case 0:
{
lean_object* v_key_4104_; lean_object* v_val_4105_; lean_object* v___x_4106_; 
v_key_4104_ = lean_ctor_get(v___x_4103_, 0);
v_val_4105_ = lean_ctor_get(v___x_4103_, 1);
lean_inc_ref(v_f_4086_);
lean_inc(v___y_4092_);
lean_inc_ref(v___y_4091_);
lean_inc(v_val_4105_);
lean_inc(v_key_4104_);
v___x_4106_ = lean_apply_6(v_f_4086_, v_b_4090_, v_key_4104_, v_val_4105_, v___y_4091_, v___y_4092_, lean_box(0));
v___y_4100_ = v___x_4106_;
goto v___jp_4099_;
}
case 1:
{
lean_object* v_node_4107_; lean_object* v___x_4108_; 
v_node_4107_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_node_4107_);
lean_inc_ref(v_f_4086_);
v___x_4108_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4086_, v_node_4107_, v_b_4090_, v___y_4091_, v___y_4092_);
v___y_4100_ = v___x_4108_;
goto v___jp_4099_;
}
default: 
{
v_a_4095_ = v_b_4090_;
goto v___jp_4094_;
}
}
}
else
{
lean_object* v___x_4109_; 
lean_dec_ref(v_f_4086_);
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_b_4090_);
return v___x_4109_;
}
v___jp_4094_:
{
size_t v___x_4096_; size_t v___x_4097_; 
v___x_4096_ = ((size_t)1ULL);
v___x_4097_ = lean_usize_add(v_i_4088_, v___x_4096_);
v_i_4088_ = v___x_4097_;
v_b_4090_ = v_a_4095_;
goto _start;
}
v___jp_4099_:
{
if (lean_obj_tag(v___y_4100_) == 0)
{
lean_object* v_a_4101_; 
v_a_4101_ = lean_ctor_get(v___y_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___y_4100_, 1);
v_a_4095_ = v_a_4101_;
goto v___jp_4094_;
}
else
{
lean_dec_ref(v_f_4086_);
return v___y_4100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4110_, lean_object* v_as_4111_, lean_object* v_i_4112_, lean_object* v_stop_4113_, lean_object* v_b_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
size_t v_i_boxed_4118_; size_t v_stop_boxed_4119_; lean_object* v_res_4120_; 
v_i_boxed_4118_ = lean_unbox_usize(v_i_4112_);
lean_dec(v_i_4112_);
v_stop_boxed_4119_ = lean_unbox_usize(v_stop_4113_);
lean_dec(v_stop_4113_);
v_res_4120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4110_, v_as_4111_, v_i_boxed_4118_, v_stop_boxed_4119_, v_b_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec_ref(v_as_4111_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4121_, lean_object* v_x_4122_, lean_object* v_x_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4121_, v_x_4122_, v_x_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4128_, lean_object* v_x_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
lean_inc(v___y_4133_);
lean_inc_ref(v___y_4132_);
v___x_4135_ = lean_apply_5(v_f_4128_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, lean_box(0));
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4136_, lean_object* v_x_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4136_, v_x_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4144_, lean_object* v_f_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v___f_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___f_4149_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4149_, 0, v_f_4145_);
v___x_4150_ = lean_box(0);
v___x_4151_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4149_, v_map_4144_, v___x_4150_, v___y_4146_, v___y_4147_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4152_, lean_object* v_f_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4152_, v_f_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
return v_res_4157_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4160_ = l_Lean_stringToMessageData(v___x_4159_);
return v___x_4160_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4162_ = l_Lean_stringToMessageData(v___x_4161_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4163_, lean_object* v_declName_4164_, lean_object* v_as_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
if (lean_obj_tag(v_as_4165_) == 0)
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
lean_dec(v_declName_4164_);
v___x_4169_ = lean_box(0);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
return v___x_4170_;
}
else
{
lean_object* v_head_4171_; lean_object* v_tail_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4202_; 
v_head_4171_ = lean_ctor_get(v_as_4165_, 0);
v_tail_4172_ = lean_ctor_get(v_as_4165_, 1);
v_isSharedCheck_4202_ = !lean_is_exclusive(v_as_4165_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4174_ = v_as_4165_;
v_isShared_4175_ = v_isSharedCheck_4202_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_tail_4172_);
lean_inc(v_head_4171_);
lean_dec(v_as_4165_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4202_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___y_4177_; lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_Parser_addToken(v_head_4171_, v_attrKind_4163_, v___y_4166_, v___y_4167_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_del_object(v___x_4174_);
v___y_4177_ = v___x_4179_;
goto v___jp_4176_;
}
else
{
lean_object* v_a_4180_; uint8_t v___y_4182_; uint8_t v___x_4200_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
v___x_4200_ = l_Lean_Exception_isInterrupt(v_a_4180_);
if (v___x_4200_ == 0)
{
uint8_t v___x_4201_; 
lean_inc(v_a_4180_);
v___x_4201_ = l_Lean_Exception_isRuntime(v_a_4180_);
v___y_4182_ = v___x_4201_;
goto v___jp_4181_;
}
else
{
v___y_4182_ = v___x_4200_;
goto v___jp_4181_;
}
v___jp_4181_:
{
if (v___y_4182_ == 0)
{
if (lean_obj_tag(v_a_4180_) == 0)
{
lean_object* v_msg_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4198_; 
lean_dec_ref_known(v___x_4179_, 1);
v_msg_4183_ = lean_ctor_get(v_a_4180_, 1);
v_isSharedCheck_4198_ = !lean_is_exclusive(v_a_4180_);
if (v_isSharedCheck_4198_ == 0)
{
lean_object* v_unused_4199_; 
v_unused_4199_ = lean_ctor_get(v_a_4180_, 0);
lean_dec(v_unused_4199_);
v___x_4185_ = v_a_4180_;
v_isShared_4186_ = v_isSharedCheck_4198_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_msg_4183_);
lean_dec(v_a_4180_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4198_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4187_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4164_);
v___x_4188_ = l_Lean_MessageData_ofConstName(v_declName_4164_, v___y_4182_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set_tag(v___x_4185_, 7);
lean_ctor_set(v___x_4185_, 1, v___x_4188_);
lean_ctor_set(v___x_4185_, 0, v___x_4187_);
v___x_4190_ = v___x_4185_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4187_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4191_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4175_ == 0)
{
lean_ctor_set_tag(v___x_4174_, 7);
lean_ctor_set(v___x_4174_, 1, v___x_4191_);
lean_ctor_set(v___x_4174_, 0, v___x_4190_);
v___x_4193_ = v___x_4174_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4190_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
lean_ctor_set(v___x_4194_, 1, v_msg_4183_);
v___x_4195_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4194_, v___y_4166_, v___y_4167_);
v___y_4177_ = v___x_4195_;
goto v___jp_4176_;
}
}
}
}
else
{
lean_dec(v_a_4180_);
lean_del_object(v___x_4174_);
v___y_4177_ = v___x_4179_;
goto v___jp_4176_;
}
}
else
{
lean_dec(v_a_4180_);
lean_del_object(v___x_4174_);
v___y_4177_ = v___x_4179_;
goto v___jp_4176_;
}
}
}
v___jp_4176_:
{
if (lean_obj_tag(v___y_4177_) == 0)
{
lean_dec_ref_known(v___y_4177_, 1);
v_as_4165_ = v_tail_4172_;
goto _start;
}
else
{
lean_dec(v_tail_4172_);
lean_dec(v_declName_4164_);
return v___y_4177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4203_, lean_object* v_declName_4204_, lean_object* v_as_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
uint8_t v_attrKind_boxed_4209_; lean_object* v_res_4210_; 
v_attrKind_boxed_4209_ = lean_unbox(v_attrKind_4203_);
v_res_4210_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4209_, v_declName_4204_, v_as_4205_, v___y_4206_, v___y_4207_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4212_, lean_object* v_declName_4213_, lean_object* v_stx_4214_, uint8_t v_attrKind_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_){
_start:
{
lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___x_4224_; 
v___x_4224_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4214_, v_a_4216_, v_a_4217_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v_env_4228_; lean_object* v___x_4229_; lean_object* v_ext_4230_; lean_object* v_toEnvExtension_4231_; lean_object* v_asyncMode_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v_categories_4235_; lean_object* v_env_4236_; lean_object* v_options_4237_; lean_object* v_ref_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v___x_4224_, 1);
v___x_4226_ = lean_st_ref_get(v_a_4217_);
v___x_4227_ = lean_st_ref_get(v_a_4217_);
v_env_4228_ = lean_ctor_get(v___x_4226_, 0);
lean_inc_ref(v_env_4228_);
lean_dec(v___x_4226_);
v___x_4229_ = l_Lean_Parser_parserExtension;
v_ext_4230_ = lean_ctor_get(v___x_4229_, 1);
v_toEnvExtension_4231_ = lean_ctor_get(v_ext_4230_, 0);
v_asyncMode_4232_ = lean_ctor_get(v_toEnvExtension_4231_, 2);
v___x_4233_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4234_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4233_, v___x_4229_, v_env_4228_, v_asyncMode_4232_);
v_categories_4235_ = lean_ctor_get(v___x_4234_, 2);
lean_inc_ref_n(v_categories_4235_, 2);
lean_dec(v___x_4234_);
v_env_4236_ = lean_ctor_get(v___x_4227_, 0);
lean_inc_ref(v_env_4236_);
lean_dec(v___x_4227_);
v_options_4237_ = lean_ctor_get(v_a_4216_, 2);
v_ref_4238_ = lean_ctor_get(v_a_4216_, 5);
lean_inc_ref(v_options_4237_);
v___x_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4239_, 0, v_env_4236_);
lean_ctor_set(v___x_4239_, 1, v_options_4237_);
lean_inc(v_declName_4213_);
v___x_4240_ = l_Lean_Parser_mkParserOfConstant(v_categories_4235_, v_declName_4213_, v___x_4239_);
lean_dec_ref_known(v___x_4239_, 2);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v_snd_4242_; lean_object* v_info_4243_; lean_object* v_fst_4244_; lean_object* v_collectTokens_4245_; lean_object* v_collectKinds_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref_known(v___x_4240_, 1);
v_snd_4242_ = lean_ctor_get(v_a_4241_, 1);
lean_inc(v_snd_4242_);
v_info_4243_ = lean_ctor_get(v_snd_4242_, 0);
v_fst_4244_ = lean_ctor_get(v_a_4241_, 0);
lean_inc(v_fst_4244_);
lean_dec(v_a_4241_);
v_collectTokens_4245_ = lean_ctor_get(v_info_4243_, 0);
v_collectKinds_4246_ = lean_ctor_get(v_info_4243_, 1);
v___x_4247_ = lean_box(0);
lean_inc_ref(v_collectTokens_4245_);
v___x_4248_ = lean_apply_1(v_collectTokens_4245_, v___x_4247_);
lean_inc(v_declName_4213_);
v___x_4249_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4215_, v_declName_4213_, v___x_4248_, v_a_4216_, v_a_4217_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v___f_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_dec_ref_known(v___x_4249_, 1);
v___f_4250_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4251_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4246_);
v___x_4252_ = lean_apply_1(v_collectKinds_4246_, v___x_4251_);
v___x_4253_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4252_, v___f_4250_, v_a_4216_, v_a_4217_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v___x_4254_; uint8_t v___x_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; 
lean_dec_ref_known(v___x_4253_, 1);
lean_inc(v_a_4225_);
lean_inc(v_snd_4242_);
lean_inc_n(v_declName_4213_, 2);
lean_inc_n(v_catName_4212_, 2);
v___x_4254_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4254_, 0, v_catName_4212_);
lean_ctor_set(v___x_4254_, 1, v_declName_4213_);
lean_ctor_set(v___x_4254_, 2, v_snd_4242_);
lean_ctor_set(v___x_4254_, 3, v_a_4225_);
v___x_4255_ = lean_unbox(v_fst_4244_);
lean_ctor_set_uint8(v___x_4254_, sizeof(void*)*4, v___x_4255_);
v___x_4256_ = lean_unbox(v_fst_4244_);
lean_dec(v_fst_4244_);
v___x_4257_ = l_Lean_Parser_addParser(v_categories_4235_, v_catName_4212_, v_declName_4213_, v___x_4256_, v_snd_4242_, v_a_4225_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref_known(v___x_4254_, 4);
lean_dec(v_declName_4213_);
lean_dec(v_catName_4212_);
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4260_ = v___x_4257_;
v_isShared_4261_ = v_isSharedCheck_4267_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4267_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
lean_ctor_set_tag(v___x_4260_, 3);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4264_ = l_Lean_MessageData_ofFormat(v___x_4263_);
v___x_4265_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4264_, v_a_4216_, v_a_4217_);
return v___x_4265_;
}
}
}
else
{
lean_object* v___x_4268_; 
lean_dec_ref_known(v___x_4257_, 1);
v___x_4268_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4229_, v___x_4254_, v_attrKind_4215_, v_a_4216_, v_a_4217_);
lean_dec_ref(v___x_4268_);
v___y_4220_ = v_a_4216_;
v___y_4221_ = v_a_4217_;
goto v___jp_4219_;
}
}
else
{
lean_dec(v_fst_4244_);
lean_dec(v_snd_4242_);
lean_dec_ref(v_categories_4235_);
lean_dec(v_a_4225_);
lean_dec(v_declName_4213_);
lean_dec(v_catName_4212_);
return v___x_4253_;
}
}
else
{
lean_dec(v_fst_4244_);
lean_dec(v_snd_4242_);
lean_dec_ref(v_categories_4235_);
lean_dec(v_a_4225_);
lean_dec(v_declName_4213_);
lean_dec(v_catName_4212_);
return v___x_4249_;
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4280_; 
lean_dec_ref(v_categories_4235_);
lean_dec(v_a_4225_);
lean_dec(v_declName_4213_);
lean_dec(v_catName_4212_);
v_a_4269_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4271_ = v___x_4240_;
v_isShared_4272_ = v_isSharedCheck_4280_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4240_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4280_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4273_ = lean_io_error_to_string(v_a_4269_);
v___x_4274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
v___x_4275_ = l_Lean_MessageData_ofFormat(v___x_4274_);
lean_inc(v_ref_4238_);
v___x_4276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4276_, 0, v_ref_4238_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4276_);
v___x_4278_ = v___x_4271_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_declName_4213_);
lean_dec(v_catName_4212_);
v_a_4281_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4224_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4224_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
v___jp_4219_:
{
uint8_t v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = 0;
v___x_4223_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4212_, v_declName_4213_, v___x_4222_, v___y_4220_, v___y_4221_);
return v___x_4223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4289_, lean_object* v_declName_4290_, lean_object* v_stx_4291_, lean_object* v_attrKind_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
uint8_t v_attrKind_boxed_4296_; lean_object* v_res_4297_; 
v_attrKind_boxed_4296_ = lean_unbox(v_attrKind_4292_);
v_res_4297_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4289_, v_declName_4290_, v_stx_4291_, v_attrKind_boxed_4296_, v_a_4293_, v_a_4294_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4298_, lean_object* v_catName_4299_, lean_object* v_declName_4300_, lean_object* v_stx_4301_, uint8_t v_attrKind_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4299_, v_declName_4300_, v_stx_4301_, v_attrKind_4302_, v_a_4303_, v_a_4304_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4307_, lean_object* v_catName_4308_, lean_object* v_declName_4309_, lean_object* v_stx_4310_, lean_object* v_attrKind_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_){
_start:
{
uint8_t v_attrKind_boxed_4315_; lean_object* v_res_4316_; 
v_attrKind_boxed_4315_ = lean_unbox(v_attrKind_4311_);
v_res_4316_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4307_, v_catName_4308_, v_declName_4309_, v_stx_4310_, v_attrKind_boxed_4315_, v_a_4312_, v_a_4313_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v___attrName_4307_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4317_, lean_object* v_map_4318_, lean_object* v_f_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4318_, v_f_4319_, v___y_4320_, v___y_4321_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4324_, lean_object* v_map_4325_, lean_object* v_f_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4324_, v_map_4325_, v_f_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4331_, lean_object* v_f_4332_, lean_object* v_init_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4332_, v_map_4331_, v_init_4333_, v___y_4334_, v___y_4335_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4338_, lean_object* v_f_4339_, lean_object* v_init_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4338_, v_f_4339_, v_init_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4345_, lean_object* v_00_u03b2_4346_, lean_object* v_map_4347_, lean_object* v_f_4348_, lean_object* v_init_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4348_, v_map_4347_, v_init_4349_, v___y_4350_, v___y_4351_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4354_, lean_object* v_00_u03b2_4355_, lean_object* v_map_4356_, lean_object* v_f_4357_, lean_object* v_init_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4354_, v_00_u03b2_4355_, v_map_4356_, v_f_4357_, v_init_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4363_, lean_object* v_00_u03b1_4364_, lean_object* v_00_u03b2_4365_, lean_object* v_f_4366_, lean_object* v_x_4367_, lean_object* v_x_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4366_, v_x_4367_, v_x_4368_, v___y_4369_, v___y_4370_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4373_, lean_object* v_00_u03b1_4374_, lean_object* v_00_u03b2_4375_, lean_object* v_f_4376_, lean_object* v_x_4377_, lean_object* v_x_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4373_, v_00_u03b1_4374_, v_00_u03b2_4375_, v_f_4376_, v_x_4377_, v_x_4378_, v___y_4379_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4383_, lean_object* v_00_u03b2_4384_, lean_object* v_00_u03c3_4385_, lean_object* v_f_4386_, lean_object* v_as_4387_, size_t v_i_4388_, size_t v_stop_4389_, lean_object* v_b_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4386_, v_as_4387_, v_i_4388_, v_stop_4389_, v_b_4390_, v___y_4391_, v___y_4392_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4395_, lean_object* v_00_u03b2_4396_, lean_object* v_00_u03c3_4397_, lean_object* v_f_4398_, lean_object* v_as_4399_, lean_object* v_i_4400_, lean_object* v_stop_4401_, lean_object* v_b_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
size_t v_i_boxed_4406_; size_t v_stop_boxed_4407_; lean_object* v_res_4408_; 
v_i_boxed_4406_ = lean_unbox_usize(v_i_4400_);
lean_dec(v_i_4400_);
v_stop_boxed_4407_ = lean_unbox_usize(v_stop_4401_);
lean_dec(v_stop_4401_);
v_res_4408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4395_, v_00_u03b2_4396_, v_00_u03c3_4397_, v_f_4398_, v_as_4399_, v_i_boxed_4406_, v_stop_boxed_4407_, v_b_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec_ref(v_as_4399_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4409_, lean_object* v_00_u03b1_4410_, lean_object* v_00_u03b2_4411_, lean_object* v_f_4412_, lean_object* v_keys_4413_, lean_object* v_vals_4414_, lean_object* v_heq_4415_, lean_object* v_i_4416_, lean_object* v_acc_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4412_, v_keys_4413_, v_vals_4414_, v_i_4416_, v_acc_4417_, v___y_4418_, v___y_4419_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4422_, lean_object* v_00_u03b1_4423_, lean_object* v_00_u03b2_4424_, lean_object* v_f_4425_, lean_object* v_keys_4426_, lean_object* v_vals_4427_, lean_object* v_heq_4428_, lean_object* v_i_4429_, lean_object* v_acc_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4422_, v_00_u03b1_4423_, v_00_u03b2_4424_, v_f_4425_, v_keys_4426_, v_vals_4427_, v_heq_4428_, v_i_4429_, v_acc_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec_ref(v_vals_4427_);
lean_dec_ref(v_keys_4426_);
return v_res_4434_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4436_, lean_object* v_declName_4437_, lean_object* v_stx_4438_, uint8_t v_attrKind_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4436_, v_declName_4437_, v_stx_4438_, v_attrKind_4439_, v___y_4440_, v___y_4441_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4444_, lean_object* v_declName_4445_, lean_object* v_stx_4446_, lean_object* v_attrKind_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v_attrKind_boxed_4451_; lean_object* v_res_4452_; 
v_attrKind_boxed_4451_ = lean_unbox(v_attrKind_4447_);
v_res_4452_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4444_, v_declName_4445_, v_stx_4446_, v_attrKind_boxed_4451_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4454_, lean_object* v_catName_4455_, lean_object* v_ref_4456_){
_start:
{
lean_object* v___f_4457_; lean_object* v___f_4458_; lean_object* v___x_4459_; uint8_t v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___f_4457_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4457_, 0, v_catName_4455_);
lean_inc(v_attrName_4454_);
v___f_4458_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4458_, 0, v_attrName_4454_);
v___x_4459_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4460_ = 1;
v___x_4461_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4461_, 0, v_ref_4456_);
lean_ctor_set(v___x_4461_, 1, v_attrName_4454_);
lean_ctor_set(v___x_4461_, 2, v___x_4459_);
lean_ctor_set_uint8(v___x_4461_, sizeof(void*)*3, v___x_4460_);
v___x_4462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
lean_ctor_set(v___x_4462_, 1, v___f_4457_);
lean_ctor_set(v___x_4462_, 2, v___f_4458_);
return v___x_4462_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4464_, lean_object* v_catName_4465_, lean_object* v_ref_4466_){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4464_, v_catName_4465_, v_ref_4466_);
v___x_4469_ = l_Lean_registerBuiltinAttribute(v___x_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4470_, lean_object* v_catName_4471_, lean_object* v_ref_4472_, lean_object* v_a_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4470_, v_catName_4471_, v_ref_4472_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4478_, lean_object* v_args_4479_){
_start:
{
if (lean_obj_tag(v_args_4479_) == 1)
{
lean_object* v_head_4482_; 
v_head_4482_ = lean_ctor_get(v_args_4479_, 0);
lean_inc(v_head_4482_);
if (lean_obj_tag(v_head_4482_) == 2)
{
lean_object* v_tail_4483_; 
v_tail_4483_ = lean_ctor_get(v_args_4479_, 1);
lean_inc(v_tail_4483_);
lean_dec_ref_known(v_args_4479_, 2);
if (lean_obj_tag(v_tail_4483_) == 1)
{
lean_object* v_head_4484_; 
v_head_4484_ = lean_ctor_get(v_tail_4483_, 0);
lean_inc(v_head_4484_);
if (lean_obj_tag(v_head_4484_) == 2)
{
lean_object* v_tail_4485_; 
v_tail_4485_ = lean_ctor_get(v_tail_4483_, 1);
lean_inc(v_tail_4485_);
lean_dec_ref_known(v_tail_4483_, 2);
if (lean_obj_tag(v_tail_4485_) == 0)
{
lean_object* v_v_4486_; lean_object* v_v_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4495_; 
v_v_4486_ = lean_ctor_get(v_head_4482_, 0);
lean_inc(v_v_4486_);
lean_dec_ref_known(v_head_4482_, 1);
v_v_4487_ = lean_ctor_get(v_head_4484_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_head_4484_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4489_ = v_head_4484_;
v_isShared_4490_ = v_isSharedCheck_4495_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_v_4487_);
lean_dec(v_head_4484_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4495_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4491_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4486_, v_v_4487_, v_ref_4478_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set_tag(v___x_4489_, 1);
lean_ctor_set(v___x_4489_, 0, v___x_4491_);
v___x_4493_ = v___x_4489_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4491_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
else
{
lean_dec(v_tail_4485_);
lean_dec_ref_known(v_head_4484_, 1);
lean_dec_ref_known(v_head_4482_, 1);
lean_dec(v_ref_4478_);
goto v___jp_4480_;
}
}
else
{
lean_dec(v_head_4484_);
lean_dec_ref_known(v_tail_4483_, 2);
lean_dec_ref_known(v_head_4482_, 1);
lean_dec(v_ref_4478_);
goto v___jp_4480_;
}
}
else
{
lean_dec_ref_known(v_head_4482_, 1);
lean_dec(v_tail_4483_);
lean_dec(v_ref_4478_);
goto v___jp_4480_;
}
}
else
{
lean_dec_ref_known(v_args_4479_, 2);
lean_dec(v_head_4482_);
lean_dec(v_ref_4478_);
goto v___jp_4480_;
}
}
else
{
lean_dec(v_args_4479_);
lean_dec(v_ref_4478_);
goto v___jp_4480_;
}
v___jp_4480_:
{
lean_object* v___x_4481_; 
v___x_4481_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___f_4501_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4502_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4503_ = l_Lean_registerAttributeImplBuilder(v___x_4502_, v___f_4501_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4505_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4507_, lean_object* v_attrName_4508_, lean_object* v_catName_4509_, uint8_t v_behavior_4510_, lean_object* v_ref_4511_){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
lean_inc(v_ref_4511_);
lean_inc(v_catName_4509_);
v___x_4513_ = l_Lean_Parser_addParserCategory(v_env_4507_, v_catName_4509_, v_ref_4511_, v_behavior_4510_);
v___x_4514_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4513_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4528_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4517_ = v___x_4514_;
v_isShared_4518_ = v_isSharedCheck_4528_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4514_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4528_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4519_; lean_object* v___x_4521_; 
v___x_4519_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4518_ == 0)
{
lean_ctor_set_tag(v___x_4517_, 2);
lean_ctor_set(v___x_4517_, 0, v_attrName_4508_);
v___x_4521_ = v___x_4517_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_attrName_4508_);
v___x_4521_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4522_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4522_, 0, v_catName_4509_);
v___x_4523_ = lean_box(0);
v___x_4524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4522_);
lean_ctor_set(v___x_4524_, 1, v___x_4523_);
v___x_4525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4521_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
v___x_4526_ = l_Lean_registerAttributeOfBuilder(v_a_4515_, v___x_4519_, v_ref_4511_, v___x_4525_);
return v___x_4526_;
}
}
}
else
{
lean_dec(v_ref_4511_);
lean_dec(v_catName_4509_);
lean_dec(v_attrName_4508_);
return v___x_4514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4529_, lean_object* v_attrName_4530_, lean_object* v_catName_4531_, lean_object* v_behavior_4532_, lean_object* v_ref_4533_, lean_object* v_a_4534_){
_start:
{
uint8_t v_behavior_boxed_4535_; lean_object* v_res_4536_; 
v_behavior_boxed_4535_ = lean_unbox(v_behavior_4532_);
v_res_4536_ = l_Lean_Parser_registerParserCategory(v_env_4529_, v_attrName_4530_, v_catName_4531_, v_behavior_boxed_4535_, v_ref_4533_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; uint8_t v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4559_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4560_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4561_ = 0;
v___x_4562_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4563_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4559_, v___x_4560_, v___x_4561_, v___x_4562_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4565_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4571_ = lean_unsigned_to_nat(3431364690u);
v___x_4572_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4573_ = l_Lean_Name_num___override(v___x_4572_, v___x_4571_);
return v___x_4573_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4574_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4575_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4576_ = l_Lean_Name_str___override(v___x_4575_, v___x_4574_);
return v___x_4576_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4577_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4578_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4579_ = l_Lean_Name_str___override(v___x_4578_, v___x_4577_);
return v___x_4579_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4580_ = lean_unsigned_to_nat(2u);
v___x_4581_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4582_ = l_Lean_Name_num___override(v___x_4581_, v___x_4580_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4584_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4585_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4586_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4587_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4584_, v___x_4585_, v___x_4586_);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4589_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4599_ = lean_unsigned_to_nat(2342493449u);
v___x_4600_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4601_ = l_Lean_Name_num___override(v___x_4600_, v___x_4599_);
return v___x_4601_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4602_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4603_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4604_ = l_Lean_Name_str___override(v___x_4603_, v___x_4602_);
return v___x_4604_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4605_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4606_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4607_ = l_Lean_Name_str___override(v___x_4606_, v___x_4605_);
return v___x_4607_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4608_ = lean_unsigned_to_nat(2u);
v___x_4609_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4610_ = l_Lean_Name_num___override(v___x_4609_, v___x_4608_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; uint8_t v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4612_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4613_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4614_ = 0;
v___x_4615_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4616_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4612_, v___x_4613_, v___x_4614_, v___x_4615_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4618_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = lean_unsigned_to_nat(3226070615u);
v___x_4625_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4626_ = l_Lean_Name_num___override(v___x_4625_, v___x_4624_);
return v___x_4626_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4627_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4628_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4629_ = l_Lean_Name_str___override(v___x_4628_, v___x_4627_);
return v___x_4629_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4630_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4631_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4632_ = l_Lean_Name_str___override(v___x_4631_, v___x_4630_);
return v___x_4632_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4633_ = lean_unsigned_to_nat(2u);
v___x_4634_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4635_ = l_Lean_Name_num___override(v___x_4634_, v___x_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4637_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4638_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4639_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4640_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4637_, v___x_4638_, v___x_4639_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4643_){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4645_ = l_Lean_Parser_categoryParser(v___x_4644_, v_rbp_4643_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4646_, lean_object* v_x_4647_, lean_object* v_x_4648_){
_start:
{
if (lean_obj_tag(v_x_4648_) == 0)
{
return v_x_4647_;
}
else
{
lean_object* v_head_4649_; lean_object* v_tail_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4673_; 
v_head_4649_ = lean_ctor_get(v_x_4648_, 0);
v_tail_4650_ = lean_ctor_get(v_x_4648_, 1);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_x_4648_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4652_ = v_x_4648_;
v_isShared_4653_ = v_isSharedCheck_4673_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_tail_4650_);
lean_inc(v_head_4649_);
lean_dec(v_x_4648_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4673_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v_fst_4654_; lean_object* v_snd_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4672_; 
v_fst_4654_ = lean_ctor_get(v_x_4647_, 0);
v_snd_4655_ = lean_ctor_get(v_x_4647_, 1);
v_isSharedCheck_4672_ = !lean_is_exclusive(v_x_4647_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4657_ = v_x_4647_;
v_isShared_4658_ = v_isSharedCheck_4672_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_snd_4655_);
lean_inc(v_fst_4654_);
lean_dec(v_x_4647_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4672_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___y_4660_; 
if (v_addOpenSimple_4646_ == 0)
{
lean_del_object(v___x_4652_);
v___y_4660_ = v_snd_4655_;
goto v___jp_4659_;
}
else
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4670_; 
v___x_4667_ = lean_box(0);
lean_inc(v_head_4649_);
v___x_4668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4668_, 0, v_head_4649_);
lean_ctor_set(v___x_4668_, 1, v___x_4667_);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 1, v_snd_4655_);
lean_ctor_set(v___x_4652_, 0, v___x_4668_);
v___x_4670_ = v___x_4652_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v___x_4668_);
lean_ctor_set(v_reuseFailAlloc_4671_, 1, v_snd_4655_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
v___y_4660_ = v___x_4670_;
goto v___jp_4659_;
}
}
v___jp_4659_:
{
lean_object* v___x_4661_; lean_object* v_env_4662_; lean_object* v___x_4664_; 
v___x_4661_ = l_Lean_Parser_parserExtension;
v_env_4662_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4661_, v_fst_4654_, v_head_4649_);
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 1, v___y_4660_);
lean_ctor_set(v___x_4657_, 0, v_env_4662_);
v___x_4664_ = v___x_4657_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_env_4662_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v___y_4660_);
v___x_4664_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
v_x_4647_ = v___x_4664_;
v_x_4648_ = v_tail_4650_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4674_, lean_object* v_x_4675_, lean_object* v_x_4676_){
_start:
{
uint8_t v_addOpenSimple_boxed_4677_; lean_object* v_res_4678_; 
v_addOpenSimple_boxed_4677_ = lean_unbox(v_addOpenSimple_4674_);
v_res_4678_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4677_, v_x_4675_, v_x_4676_);
return v_res_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4679_, lean_object* v_as_4680_, size_t v_i_4681_, size_t v_stop_4682_, lean_object* v_b_4683_){
_start:
{
uint8_t v___x_4684_; 
v___x_4684_ = lean_usize_dec_eq(v_i_4681_, v_stop_4682_);
if (v___x_4684_ == 0)
{
lean_object* v_toParserModuleContext_4685_; lean_object* v_toInputContext_4686_; lean_object* v_toCacheableParserContext_4687_; lean_object* v_tokens_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4715_; 
v_toParserModuleContext_4685_ = lean_ctor_get(v_b_4683_, 1);
v_toInputContext_4686_ = lean_ctor_get(v_b_4683_, 0);
v_toCacheableParserContext_4687_ = lean_ctor_get(v_b_4683_, 2);
v_tokens_4688_ = lean_ctor_get(v_b_4683_, 3);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_b_4683_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4690_ = v_b_4683_;
v_isShared_4691_ = v_isSharedCheck_4715_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_tokens_4688_);
lean_inc(v_toCacheableParserContext_4687_);
lean_inc(v_toParserModuleContext_4685_);
lean_inc(v_toInputContext_4686_);
lean_dec(v_b_4683_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4715_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v_env_4692_; lean_object* v_options_4693_; lean_object* v_currNamespace_4694_; lean_object* v_openDecls_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4714_; 
v_env_4692_ = lean_ctor_get(v_toParserModuleContext_4685_, 0);
v_options_4693_ = lean_ctor_get(v_toParserModuleContext_4685_, 1);
v_currNamespace_4694_ = lean_ctor_get(v_toParserModuleContext_4685_, 2);
v_openDecls_4695_ = lean_ctor_get(v_toParserModuleContext_4685_, 3);
v_isSharedCheck_4714_ = !lean_is_exclusive(v_toParserModuleContext_4685_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4697_ = v_toParserModuleContext_4685_;
v_isShared_4698_ = v_isSharedCheck_4714_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_openDecls_4695_);
lean_inc(v_currNamespace_4694_);
lean_inc(v_options_4693_);
lean_inc(v_env_4692_);
lean_dec(v_toParserModuleContext_4685_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4714_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4699_; lean_object* v_nss_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v_fst_4703_; lean_object* v_snd_4704_; lean_object* v___x_4706_; 
v___x_4699_ = lean_array_uget_borrowed(v_as_4680_, v_i_4681_);
lean_inc(v___x_4699_);
lean_inc(v_openDecls_4695_);
lean_inc(v_currNamespace_4694_);
lean_inc_ref(v_env_4692_);
v_nss_4700_ = l_Lean_ResolveName_resolveNamespace(v_env_4692_, v_currNamespace_4694_, v_openDecls_4695_, v___x_4699_);
v___x_4701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4701_, 0, v_env_4692_);
lean_ctor_set(v___x_4701_, 1, v_openDecls_4695_);
v___x_4702_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4679_, v___x_4701_, v_nss_4700_);
v_fst_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_fst_4703_);
v_snd_4704_ = lean_ctor_get(v___x_4702_, 1);
lean_inc(v_snd_4704_);
lean_dec_ref(v___x_4702_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 3, v_snd_4704_);
lean_ctor_set(v___x_4697_, 0, v_fst_4703_);
v___x_4706_ = v___x_4697_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_fst_4703_);
lean_ctor_set(v_reuseFailAlloc_4713_, 1, v_options_4693_);
lean_ctor_set(v_reuseFailAlloc_4713_, 2, v_currNamespace_4694_);
lean_ctor_set(v_reuseFailAlloc_4713_, 3, v_snd_4704_);
v___x_4706_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
lean_object* v___x_4708_; 
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 1, v___x_4706_);
v___x_4708_ = v___x_4690_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_toInputContext_4686_);
lean_ctor_set(v_reuseFailAlloc_4712_, 1, v___x_4706_);
lean_ctor_set(v_reuseFailAlloc_4712_, 2, v_toCacheableParserContext_4687_);
lean_ctor_set(v_reuseFailAlloc_4712_, 3, v_tokens_4688_);
v___x_4708_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
size_t v___x_4709_; size_t v___x_4710_; 
v___x_4709_ = ((size_t)1ULL);
v___x_4710_ = lean_usize_add(v_i_4681_, v___x_4709_);
v_i_4681_ = v___x_4710_;
v_b_4683_ = v___x_4708_;
goto _start;
}
}
}
}
}
else
{
return v_b_4683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4716_, lean_object* v_as_4717_, lean_object* v_i_4718_, lean_object* v_stop_4719_, lean_object* v_b_4720_){
_start:
{
uint8_t v_addOpenSimple_boxed_4721_; size_t v_i_boxed_4722_; size_t v_stop_boxed_4723_; lean_object* v_res_4724_; 
v_addOpenSimple_boxed_4721_ = lean_unbox(v_addOpenSimple_4716_);
v_i_boxed_4722_ = lean_unbox_usize(v_i_4718_);
lean_dec(v_i_4718_);
v_stop_boxed_4723_ = lean_unbox_usize(v_stop_4719_);
lean_dec(v_stop_4719_);
v_res_4724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4721_, v_as_4717_, v_i_boxed_4722_, v_stop_boxed_4723_, v_b_4720_);
lean_dec_ref(v_as_4717_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4725_, lean_object* v_ids_4726_, uint8_t v_addOpenSimple_4727_, lean_object* v_c_4728_){
_start:
{
lean_object* v___y_4730_; lean_object* v___x_4749_; lean_object* v___x_4750_; uint8_t v___x_4751_; 
v___x_4749_ = lean_unsigned_to_nat(0u);
v___x_4750_ = lean_array_get_size(v_ids_4726_);
v___x_4751_ = lean_nat_dec_lt(v___x_4749_, v___x_4750_);
if (v___x_4751_ == 0)
{
v___y_4730_ = v_c_4728_;
goto v___jp_4729_;
}
else
{
uint8_t v___x_4752_; 
v___x_4752_ = lean_nat_dec_le(v___x_4750_, v___x_4750_);
if (v___x_4752_ == 0)
{
if (v___x_4751_ == 0)
{
v___y_4730_ = v_c_4728_;
goto v___jp_4729_;
}
else
{
size_t v___x_4753_; size_t v___x_4754_; lean_object* v___x_4755_; 
v___x_4753_ = ((size_t)0ULL);
v___x_4754_ = lean_usize_of_nat(v___x_4750_);
v___x_4755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4727_, v_ids_4726_, v___x_4753_, v___x_4754_, v_c_4728_);
v___y_4730_ = v___x_4755_;
goto v___jp_4729_;
}
}
else
{
size_t v___x_4756_; size_t v___x_4757_; lean_object* v___x_4758_; 
v___x_4756_ = ((size_t)0ULL);
v___x_4757_ = lean_usize_of_nat(v___x_4750_);
v___x_4758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4727_, v_ids_4726_, v___x_4756_, v___x_4757_, v_c_4728_);
v___y_4730_ = v___x_4758_;
goto v___jp_4729_;
}
}
v___jp_4729_:
{
lean_object* v_toParserModuleContext_4731_; lean_object* v_toInputContext_4732_; lean_object* v_toCacheableParserContext_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4747_; 
v_toParserModuleContext_4731_ = lean_ctor_get(v___y_4730_, 1);
v_toInputContext_4732_ = lean_ctor_get(v___y_4730_, 0);
v_toCacheableParserContext_4733_ = lean_ctor_get(v___y_4730_, 2);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___y_4730_);
if (v_isSharedCheck_4747_ == 0)
{
lean_object* v_unused_4748_; 
v_unused_4748_ = lean_ctor_get(v___y_4730_, 3);
lean_dec(v_unused_4748_);
v___x_4735_ = v___y_4730_;
v_isShared_4736_ = v_isSharedCheck_4747_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_toCacheableParserContext_4733_);
lean_inc(v_toParserModuleContext_4731_);
lean_inc(v_toInputContext_4732_);
lean_dec(v___y_4730_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4747_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v_env_4737_; lean_object* v___x_4738_; lean_object* v_ext_4739_; lean_object* v_toEnvExtension_4740_; lean_object* v_asyncMode_4741_; lean_object* v___x_4742_; lean_object* v_tokens_4743_; lean_object* v___x_4745_; 
v_env_4737_ = lean_ctor_get(v_toParserModuleContext_4731_, 0);
v___x_4738_ = l_Lean_Parser_parserExtension;
v_ext_4739_ = lean_ctor_get(v___x_4738_, 1);
v_toEnvExtension_4740_ = lean_ctor_get(v_ext_4739_, 0);
v_asyncMode_4741_ = lean_ctor_get(v_toEnvExtension_4740_, 2);
lean_inc_ref(v_env_4737_);
v___x_4742_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4725_, v___x_4738_, v_env_4737_, v_asyncMode_4741_);
v_tokens_4743_ = lean_ctor_get(v___x_4742_, 0);
lean_inc_ref(v_tokens_4743_);
lean_dec(v___x_4742_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 3, v_tokens_4743_);
v___x_4745_ = v___x_4735_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_toInputContext_4732_);
lean_ctor_set(v_reuseFailAlloc_4746_, 1, v_toParserModuleContext_4731_);
lean_ctor_set(v_reuseFailAlloc_4746_, 2, v_toCacheableParserContext_4733_);
lean_ctor_set(v_reuseFailAlloc_4746_, 3, v_tokens_4743_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4759_, lean_object* v_ids_4760_, lean_object* v_addOpenSimple_4761_, lean_object* v_c_4762_){
_start:
{
uint8_t v_addOpenSimple_boxed_4763_; lean_object* v_res_4764_; 
v_addOpenSimple_boxed_4763_ = lean_unbox(v_addOpenSimple_4761_);
v_res_4764_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4759_, v_ids_4760_, v_addOpenSimple_boxed_4763_, v_c_4762_);
lean_dec_ref(v_ids_4760_);
lean_dec_ref(v___x_4759_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4765_, uint8_t v_addOpenSimple_4766_, lean_object* v_p_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___f_4772_; lean_object* v___x_4773_; 
v___x_4770_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4771_ = lean_box(v_addOpenSimple_4766_);
v___f_4772_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4772_, 0, v___x_4770_);
lean_closure_set(v___f_4772_, 1, v_ids_4765_);
lean_closure_set(v___f_4772_, 2, v___x_4771_);
v___x_4773_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4772_, v_p_4767_, v_a_4768_, v_a_4769_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4774_, lean_object* v_addOpenSimple_4775_, lean_object* v_p_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
uint8_t v_addOpenSimple_boxed_4779_; lean_object* v_res_4780_; 
v_addOpenSimple_boxed_4779_ = lean_unbox(v_addOpenSimple_4775_);
v_res_4780_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4774_, v_addOpenSimple_boxed_4779_, v_p_4776_, v_a_4777_, v_a_4778_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4781_, size_t v_i_4782_, lean_object* v_bs_4783_){
_start:
{
uint8_t v___x_4784_; 
v___x_4784_ = lean_usize_dec_lt(v_i_4782_, v_sz_4781_);
if (v___x_4784_ == 0)
{
return v_bs_4783_;
}
else
{
lean_object* v_v_4785_; lean_object* v___x_4786_; lean_object* v_bs_x27_4787_; lean_object* v___x_4788_; size_t v___x_4789_; size_t v___x_4790_; lean_object* v___x_4791_; 
v_v_4785_ = lean_array_uget(v_bs_4783_, v_i_4782_);
v___x_4786_ = lean_unsigned_to_nat(0u);
v_bs_x27_4787_ = lean_array_uset(v_bs_4783_, v_i_4782_, v___x_4786_);
v___x_4788_ = l_Lean_Syntax_getId(v_v_4785_);
lean_dec(v_v_4785_);
v___x_4789_ = ((size_t)1ULL);
v___x_4790_ = lean_usize_add(v_i_4782_, v___x_4789_);
v___x_4791_ = lean_array_uset(v_bs_x27_4787_, v_i_4782_, v___x_4788_);
v_i_4782_ = v___x_4790_;
v_bs_4783_ = v___x_4791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4793_, lean_object* v_i_4794_, lean_object* v_bs_4795_){
_start:
{
size_t v_sz_boxed_4796_; size_t v_i_boxed_4797_; lean_object* v_res_4798_; 
v_sz_boxed_4796_ = lean_unbox_usize(v_sz_4793_);
lean_dec(v_sz_4793_);
v_i_boxed_4797_ = lean_unbox_usize(v_i_4794_);
lean_dec(v_i_4794_);
v_res_4798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4796_, v_i_boxed_4797_, v_bs_4795_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4812_, lean_object* v_p_4813_, lean_object* v_c_4814_, lean_object* v_s_4815_){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
lean_inc(v_openDeclStx_4812_);
v___x_4816_ = l_Lean_Syntax_getKind(v_openDeclStx_4812_);
v___x_4817_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4818_ = lean_name_eq(v___x_4816_, v___x_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; uint8_t v___x_4820_; 
v___x_4819_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4820_ = lean_name_eq(v___x_4816_, v___x_4819_);
lean_dec(v___x_4816_);
if (v___x_4820_ == 0)
{
lean_object* v___x_4821_; 
lean_dec(v_openDeclStx_4812_);
v___x_4821_ = lean_apply_2(v_p_4813_, v_c_4814_, v_s_4815_);
return v___x_4821_;
}
else
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; size_t v_sz_4825_; size_t v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4822_ = lean_unsigned_to_nat(1u);
v___x_4823_ = l_Lean_Syntax_getArg(v_openDeclStx_4812_, v___x_4822_);
lean_dec(v_openDeclStx_4812_);
v___x_4824_ = l_Lean_Syntax_getArgs(v___x_4823_);
lean_dec(v___x_4823_);
v_sz_4825_ = lean_array_size(v___x_4824_);
v___x_4826_ = ((size_t)0ULL);
v___x_4827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4825_, v___x_4826_, v___x_4824_);
v___x_4828_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4827_, v___x_4818_, v_p_4813_, v_c_4814_, v_s_4815_);
return v___x_4828_;
}
}
else
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; size_t v_sz_4832_; size_t v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
lean_dec(v___x_4816_);
v___x_4829_ = lean_unsigned_to_nat(0u);
v___x_4830_ = l_Lean_Syntax_getArg(v_openDeclStx_4812_, v___x_4829_);
lean_dec(v_openDeclStx_4812_);
v___x_4831_ = l_Lean_Syntax_getArgs(v___x_4830_);
lean_dec(v___x_4830_);
v_sz_4832_ = lean_array_size(v___x_4831_);
v___x_4833_ = ((size_t)0ULL);
v___x_4834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4832_, v___x_4833_, v___x_4831_);
v___x_4835_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4834_, v___x_4818_, v_p_4813_, v_c_4814_, v_s_4815_);
return v___x_4835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4842_, lean_object* v_c_4843_, lean_object* v_s_4844_){
_start:
{
lean_object* v_stxStack_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; uint8_t v___x_4848_; 
v_stxStack_4845_ = lean_ctor_get(v_s_4844_, 0);
v___x_4846_ = lean_unsigned_to_nat(0u);
v___x_4847_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4845_);
v___x_4848_ = lean_nat_dec_lt(v___x_4846_, v___x_4847_);
lean_dec(v___x_4847_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; 
v___x_4849_ = lean_apply_2(v_p_4842_, v_c_4843_, v_s_4844_);
return v___x_4849_;
}
else
{
lean_object* v_stx_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; uint8_t v___x_4853_; 
v_stx_4850_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4845_);
lean_inc(v_stx_4850_);
v___x_4851_ = l_Lean_Syntax_getKind(v_stx_4850_);
v___x_4852_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4853_ = lean_name_eq(v___x_4851_, v___x_4852_);
lean_dec(v___x_4851_);
if (v___x_4853_ == 0)
{
lean_object* v___x_4854_; 
lean_dec(v_stx_4850_);
v___x_4854_ = lean_apply_2(v_p_4842_, v_c_4843_, v_s_4844_);
return v___x_4854_;
}
else
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4855_ = lean_unsigned_to_nat(1u);
v___x_4856_ = l_Lean_Syntax_getArg(v_stx_4850_, v___x_4855_);
lean_dec(v_stx_4850_);
v___x_4857_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4856_, v_p_4842_, v_c_4843_, v_s_4844_);
return v___x_4857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4858_){
_start:
{
lean_object* v_info_4859_; lean_object* v_fn_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4868_; 
v_info_4859_ = lean_ctor_get(v_p_4858_, 0);
v_fn_4860_ = lean_ctor_get(v_p_4858_, 1);
v_isSharedCheck_4868_ = !lean_is_exclusive(v_p_4858_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4862_ = v_p_4858_;
v_isShared_4863_ = v_isSharedCheck_4868_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_fn_4860_);
lean_inc(v_info_4859_);
lean_dec(v_p_4858_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4868_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4864_; lean_object* v___x_4866_; 
v___x_4864_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4864_, 0, v_fn_4860_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 1, v___x_4864_);
v___x_4866_ = v___x_4862_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_info_4859_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4869_, lean_object* v_c_4870_, lean_object* v_s_4871_){
_start:
{
lean_object* v_stxStack_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; uint8_t v___x_4875_; 
v_stxStack_4872_ = lean_ctor_get(v_s_4871_, 0);
v___x_4873_ = lean_unsigned_to_nat(0u);
v___x_4874_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4872_);
v___x_4875_ = lean_nat_dec_lt(v___x_4873_, v___x_4874_);
lean_dec(v___x_4874_);
if (v___x_4875_ == 0)
{
lean_object* v___x_4876_; 
v___x_4876_ = lean_apply_2(v_p_4869_, v_c_4870_, v_s_4871_);
return v___x_4876_;
}
else
{
lean_object* v_stx_4877_; lean_object* v___x_4878_; 
v_stx_4877_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4872_);
v___x_4878_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4877_, v_p_4869_, v_c_4870_, v_s_4871_);
return v___x_4878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4879_){
_start:
{
lean_object* v_info_4880_; lean_object* v_fn_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4889_; 
v_info_4880_ = lean_ctor_get(v_p_4879_, 0);
v_fn_4881_ = lean_ctor_get(v_p_4879_, 1);
v_isSharedCheck_4889_ = !lean_is_exclusive(v_p_4879_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4883_ = v_p_4879_;
v_isShared_4884_ = v_isSharedCheck_4889_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_fn_4881_);
lean_inc(v_info_4880_);
lean_dec(v_p_4879_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4889_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4885_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4885_, 0, v_fn_4881_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 1, v___x_4885_);
v___x_4887_ = v___x_4883_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_info_4880_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_4896_){
_start:
{
lean_object* v___x_4904_; 
v___x_4904_ = l_Lean_Syntax_isStrLit_x3f(v_val_4896_);
if (lean_obj_tag(v___x_4904_) == 1)
{
lean_object* v_val_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4913_; 
v_val_4905_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4907_ = v___x_4904_;
v_isShared_4908_ = v_isSharedCheck_4913_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_val_4905_);
lean_dec(v___x_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4913_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4909_; lean_object* v___x_4911_; 
v___x_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4909_, 0, v_val_4905_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4909_);
v___x_4911_ = v___x_4907_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
else
{
lean_object* v___x_4914_; 
lean_dec(v___x_4904_);
v___x_4914_ = l_Lean_Syntax_isNatLit_x3f(v_val_4896_);
if (lean_obj_tag(v___x_4914_) == 1)
{
lean_object* v_val_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4923_; 
v_val_4915_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4917_ = v___x_4914_;
v_isShared_4918_ = v_isSharedCheck_4923_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_val_4915_);
lean_dec(v___x_4914_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4923_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4919_; lean_object* v___x_4921_; 
v___x_4919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4919_, 0, v_val_4915_);
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 0, v___x_4919_);
v___x_4921_ = v___x_4917_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4919_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
else
{
lean_dec(v___x_4914_);
if (lean_obj_tag(v_val_4896_) == 2)
{
lean_object* v_val_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; 
v_val_4924_ = lean_ctor_get(v_val_4896_, 1);
v___x_4925_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_4926_ = lean_string_dec_eq(v_val_4924_, v___x_4925_);
if (v___x_4926_ == 0)
{
goto v___jp_4897_;
}
else
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4927_, 0, v___x_4926_);
v___x_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
return v___x_4928_;
}
}
else
{
goto v___jp_4897_;
}
}
}
v___jp_4897_:
{
if (lean_obj_tag(v_val_4896_) == 2)
{
lean_object* v_val_4898_; lean_object* v___x_4899_; uint8_t v___x_4900_; 
v_val_4898_ = lean_ctor_get(v_val_4896_, 1);
v___x_4899_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_4900_ = lean_string_dec_eq(v_val_4898_, v___x_4899_);
if (v___x_4900_ == 0)
{
lean_object* v___x_4901_; 
v___x_4901_ = lean_box(0);
return v___x_4901_;
}
else
{
lean_object* v___x_4902_; 
v___x_4902_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_4902_;
}
}
else
{
lean_object* v___x_4903_; 
v___x_4903_ = lean_box(0);
return v___x_4903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_4929_);
lean_dec(v_val_4929_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_4931_, lean_object* v_v_4932_, lean_object* v_c_4933_){
_start:
{
lean_object* v_toParserModuleContext_4934_; lean_object* v_toInputContext_4935_; lean_object* v_toCacheableParserContext_4936_; lean_object* v_tokens_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4974_; 
v_toParserModuleContext_4934_ = lean_ctor_get(v_c_4933_, 1);
v_toInputContext_4935_ = lean_ctor_get(v_c_4933_, 0);
v_toCacheableParserContext_4936_ = lean_ctor_get(v_c_4933_, 2);
v_tokens_4937_ = lean_ctor_get(v_c_4933_, 3);
v_isSharedCheck_4974_ = !lean_is_exclusive(v_c_4933_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4939_ = v_c_4933_;
v_isShared_4940_ = v_isSharedCheck_4974_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_tokens_4937_);
lean_inc(v_toCacheableParserContext_4936_);
lean_inc(v_toParserModuleContext_4934_);
lean_inc(v_toInputContext_4935_);
lean_dec(v_c_4933_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4974_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v_env_4941_; lean_object* v_options_4942_; lean_object* v_currNamespace_4943_; lean_object* v_openDecls_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4973_; 
v_env_4941_ = lean_ctor_get(v_toParserModuleContext_4934_, 0);
v_options_4942_ = lean_ctor_get(v_toParserModuleContext_4934_, 1);
v_currNamespace_4943_ = lean_ctor_get(v_toParserModuleContext_4934_, 2);
v_openDecls_4944_ = lean_ctor_get(v_toParserModuleContext_4934_, 3);
v_isSharedCheck_4973_ = !lean_is_exclusive(v_toParserModuleContext_4934_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4946_ = v_toParserModuleContext_4934_;
v_isShared_4947_ = v_isSharedCheck_4973_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_openDecls_4944_);
lean_inc(v_currNamespace_4943_);
lean_inc(v_options_4942_);
lean_inc(v_env_4941_);
lean_dec(v_toParserModuleContext_4934_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4973_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___y_4949_; lean_object* v_map_4956_; uint8_t v_hasTrace_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4972_; 
v_map_4956_ = lean_ctor_get(v_options_4942_, 0);
v_hasTrace_4957_ = lean_ctor_get_uint8(v_options_4942_, sizeof(void*)*1);
v_isSharedCheck_4972_ = !lean_is_exclusive(v_options_4942_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4959_ = v_options_4942_;
v_isShared_4960_ = v_isSharedCheck_4972_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_map_4956_);
lean_dec(v_options_4942_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4972_;
goto v_resetjp_4958_;
}
v___jp_4948_:
{
lean_object* v___x_4951_; 
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 1, v___y_4949_);
v___x_4951_ = v___x_4946_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_env_4941_);
lean_ctor_set(v_reuseFailAlloc_4955_, 1, v___y_4949_);
lean_ctor_set(v_reuseFailAlloc_4955_, 2, v_currNamespace_4943_);
lean_ctor_set(v_reuseFailAlloc_4955_, 3, v_openDecls_4944_);
v___x_4951_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
lean_object* v___x_4953_; 
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___x_4951_);
v___x_4953_ = v___x_4939_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_toInputContext_4935_);
lean_ctor_set(v_reuseFailAlloc_4954_, 1, v___x_4951_);
lean_ctor_set(v_reuseFailAlloc_4954_, 2, v_toCacheableParserContext_4936_);
lean_ctor_set(v_reuseFailAlloc_4954_, 3, v_tokens_4937_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
v_resetjp_4958_:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4961_ = l_Lean_Syntax_getId(v_nameStx_4931_);
v___x_4962_ = l_Lean_Name_eraseMacroScopes(v___x_4961_);
lean_dec(v___x_4961_);
lean_inc(v___x_4962_);
v___x_4963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4962_, v_v_4932_, v_map_4956_);
if (v_hasTrace_4957_ == 0)
{
lean_object* v___x_4964_; uint8_t v___x_4965_; lean_object* v___x_4967_; 
v___x_4964_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_4965_ = l_Lean_Name_isPrefixOf(v___x_4964_, v___x_4962_);
lean_dec(v___x_4962_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4963_);
v___x_4967_ = v___x_4959_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4963_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
lean_ctor_set_uint8(v___x_4967_, sizeof(void*)*1, v___x_4965_);
v___y_4949_ = v___x_4967_;
goto v___jp_4948_;
}
}
else
{
lean_object* v___x_4970_; 
lean_dec(v___x_4962_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4963_);
v___x_4970_ = v___x_4959_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4963_);
lean_ctor_set_uint8(v_reuseFailAlloc_4971_, sizeof(void*)*1, v_hasTrace_4957_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
v___y_4949_ = v___x_4970_;
goto v___jp_4948_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_4975_, lean_object* v_v_4976_, lean_object* v_c_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_4975_, v_v_4976_, v_c_4977_);
lean_dec(v_nameStx_4975_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_4979_, lean_object* v_valStx_4980_, lean_object* v_p_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v___x_4984_; 
v___x_4984_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_4980_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v___x_4985_; 
lean_dec(v_nameStx_4979_);
v___x_4985_ = lean_apply_2(v_p_4981_, v_a_4982_, v_a_4983_);
return v___x_4985_;
}
else
{
lean_object* v_val_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v_val_4986_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_val_4986_);
lean_dec_ref_known(v___x_4984_, 1);
v___x_4987_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_4987_, 0, v_nameStx_4979_);
lean_closure_set(v___x_4987_, 1, v_val_4986_);
v___x_4988_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_4987_, v_p_4981_, v_a_4982_, v_a_4983_);
return v___x_4988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_4989_, lean_object* v_valStx_4990_, lean_object* v_p_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_4989_, v_valStx_4990_, v_p_4991_, v_a_4992_, v_a_4993_);
lean_dec(v_valStx_4990_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_5001_, lean_object* v_c_5002_, lean_object* v_s_5003_){
_start:
{
lean_object* v_stxStack_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; uint8_t v___x_5007_; 
v_stxStack_5004_ = lean_ctor_get(v_s_5003_, 0);
v___x_5005_ = lean_unsigned_to_nat(0u);
v___x_5006_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5004_);
v___x_5007_ = lean_nat_dec_lt(v___x_5005_, v___x_5006_);
lean_dec(v___x_5006_);
if (v___x_5007_ == 0)
{
lean_object* v___x_5008_; 
v___x_5008_ = lean_apply_2(v_p_5001_, v_c_5002_, v_s_5003_);
return v___x_5008_;
}
else
{
lean_object* v_stx_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; uint8_t v___x_5012_; 
v_stx_5009_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5004_);
lean_inc(v_stx_5009_);
v___x_5010_ = l_Lean_Syntax_getKind(v_stx_5009_);
v___x_5011_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_5012_ = lean_name_eq(v___x_5010_, v___x_5011_);
lean_dec(v___x_5010_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; 
lean_dec(v_stx_5009_);
v___x_5013_ = lean_apply_2(v_p_5001_, v_c_5002_, v_s_5003_);
return v___x_5013_;
}
else
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5014_ = lean_unsigned_to_nat(1u);
v___x_5015_ = l_Lean_Syntax_getArg(v_stx_5009_, v___x_5014_);
v___x_5016_ = lean_unsigned_to_nat(3u);
v___x_5017_ = l_Lean_Syntax_getArg(v_stx_5009_, v___x_5016_);
lean_dec(v_stx_5009_);
v___x_5018_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5015_, v___x_5017_, v_p_5001_, v_c_5002_, v_s_5003_);
lean_dec(v___x_5017_);
return v___x_5018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_5019_){
_start:
{
lean_object* v_info_5020_; lean_object* v_fn_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5029_; 
v_info_5020_ = lean_ctor_get(v_p_5019_, 0);
v_fn_5021_ = lean_ctor_get(v_p_5019_, 1);
v_isSharedCheck_5029_ = !lean_is_exclusive(v_p_5019_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5023_ = v_p_5019_;
v_isShared_5024_ = v_isSharedCheck_5029_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_fn_5021_);
lean_inc(v_info_5020_);
lean_dec(v_p_5019_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5029_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5025_; lean_object* v___x_5027_; 
v___x_5025_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_5025_, 0, v_fn_5021_);
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 1, v___x_5025_);
v___x_5027_ = v___x_5023_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_info_5020_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5030_, lean_object* v_c_5031_, lean_object* v_s_5032_){
_start:
{
lean_object* v_stxStack_5033_; lean_object* v_sz_5034_; lean_object* v___x_5035_; uint8_t v___x_5036_; 
v_stxStack_5033_ = lean_ctor_get(v_s_5032_, 0);
v_sz_5034_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5033_);
v___x_5035_ = lean_unsigned_to_nat(3u);
v___x_5036_ = lean_nat_dec_le(v___x_5035_, v_sz_5034_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; 
lean_dec(v_sz_5034_);
v___x_5037_ = lean_apply_2(v_p_5030_, v_c_5031_, v_s_5032_);
return v___x_5037_;
}
else
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5038_ = lean_nat_sub(v_sz_5034_, v___x_5035_);
lean_dec(v_sz_5034_);
v___x_5039_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5033_, v___x_5038_);
lean_dec(v___x_5038_);
v___x_5040_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5033_);
v___x_5041_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5039_, v___x_5040_, v_p_5030_, v_c_5031_, v_s_5032_);
lean_dec(v___x_5040_);
return v___x_5041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5042_){
_start:
{
lean_object* v_info_5043_; lean_object* v_fn_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5052_; 
v_info_5043_ = lean_ctor_get(v_p_5042_, 0);
v_fn_5044_ = lean_ctor_get(v_p_5042_, 1);
v_isSharedCheck_5052_ = !lean_is_exclusive(v_p_5042_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5046_ = v_p_5042_;
v_isShared_5047_ = v_isSharedCheck_5052_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_fn_5044_);
lean_inc(v_info_5043_);
lean_dec(v_p_5042_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5052_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5048_; lean_object* v___x_5050_; 
v___x_5048_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5048_, 0, v_fn_5044_);
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 1, v___x_5048_);
v___x_5050_ = v___x_5046_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_info_5043_);
lean_ctor_set(v_reuseFailAlloc_5051_, 1, v___x_5048_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5053_){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5055_ = lean_st_ref_get(v___x_5053_);
v___x_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5055_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5057_);
lean_dec(v___x_5057_);
return v_res_5059_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5060_; lean_object* v___f_5061_; 
v___x_5060_ = l_Lean_Parser_parserAliasesRef;
v___f_5061_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5061_, 0, v___x_5060_);
return v___f_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___f_5063_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5064_ = lean_box(0);
v___x_5065_ = lean_box(2);
v___x_5066_ = l_Lean_registerEnvExtension___redArg(v___f_5063_, v___x_5064_, v___x_5065_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object* v_x_5069_){
_start:
{
switch(lean_obj_tag(v_x_5069_))
{
case 0:
{
lean_object* v___x_5070_; 
v___x_5070_ = lean_unsigned_to_nat(0u);
return v___x_5070_;
}
case 1:
{
lean_object* v___x_5071_; 
v___x_5071_ = lean_unsigned_to_nat(1u);
return v___x_5071_;
}
default: 
{
lean_object* v___x_5072_; 
v___x_5072_ = lean_unsigned_to_nat(2u);
return v___x_5072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object* v_x_5073_){
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l_Lean_Parser_ParserResolution_ctorIdx(v_x_5073_);
lean_dec_ref(v_x_5073_);
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5075_, lean_object* v_k_5076_){
_start:
{
switch(lean_obj_tag(v_t_5075_))
{
case 0:
{
lean_object* v_cat_5077_; lean_object* v___x_5078_; 
v_cat_5077_ = lean_ctor_get(v_t_5075_, 0);
lean_inc(v_cat_5077_);
lean_dec_ref_known(v_t_5075_, 1);
v___x_5078_ = lean_apply_1(v_k_5076_, v_cat_5077_);
return v___x_5078_;
}
case 1:
{
lean_object* v_decl_5079_; uint8_t v_isDescr_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v_decl_5079_ = lean_ctor_get(v_t_5075_, 0);
lean_inc(v_decl_5079_);
v_isDescr_5080_ = lean_ctor_get_uint8(v_t_5075_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5075_, 1);
v___x_5081_ = lean_box(v_isDescr_5080_);
v___x_5082_ = lean_apply_2(v_k_5076_, v_decl_5079_, v___x_5081_);
return v___x_5082_;
}
default: 
{
lean_object* v_p_5083_; lean_object* v___x_5084_; 
v_p_5083_ = lean_ctor_get(v_t_5075_, 0);
lean_inc_ref(v_p_5083_);
lean_dec_ref_known(v_t_5075_, 1);
v___x_5084_ = lean_apply_1(v_k_5076_, v_p_5083_);
return v___x_5084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5085_, lean_object* v_ctorIdx_5086_, lean_object* v_t_5087_, lean_object* v_h_5088_, lean_object* v_k_5089_){
_start:
{
lean_object* v___x_5090_; 
v___x_5090_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5087_, v_k_5089_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5091_, lean_object* v_ctorIdx_5092_, lean_object* v_t_5093_, lean_object* v_h_5094_, lean_object* v_k_5095_){
_start:
{
lean_object* v_res_5096_; 
v_res_5096_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5091_, v_ctorIdx_5092_, v_t_5093_, v_h_5094_, v_k_5095_);
lean_dec(v_ctorIdx_5092_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5097_, lean_object* v_category_5098_){
_start:
{
lean_object* v___x_5099_; 
v___x_5099_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5097_, v_category_5098_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5100_, lean_object* v_t_5101_, lean_object* v_h_5102_, lean_object* v_category_5103_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5101_, v_category_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5105_, lean_object* v_parser_5106_){
_start:
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5105_, v_parser_5106_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5108_, lean_object* v_t_5109_, lean_object* v_h_5110_, lean_object* v_parser_5111_){
_start:
{
lean_object* v___x_5112_; 
v___x_5112_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5109_, v_parser_5111_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5113_, lean_object* v_alias_5114_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5113_, v_alias_5114_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5116_, lean_object* v_t_5117_, lean_object* v_h_5118_, lean_object* v_alias_5119_){
_start:
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5117_, v_alias_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5124_, lean_object* v_name_5125_){
_start:
{
uint8_t v___x_5126_; lean_object* v___x_5127_; 
v___x_5126_ = 0;
v___x_5127_ = l_Lean_Environment_find_x3f(v_env_5124_, v_name_5125_, v___x_5126_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v___x_5128_; 
v___x_5128_ = lean_box(0);
return v___x_5128_;
}
else
{
lean_object* v_val_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5176_; 
v_val_5129_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5131_ = v___x_5127_;
v_isShared_5132_ = v_isSharedCheck_5176_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_val_5129_);
lean_dec(v___x_5127_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5176_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5133_; 
v___x_5133_ = l_Lean_ConstantInfo_type(v_val_5129_);
lean_dec(v_val_5129_);
if (lean_obj_tag(v___x_5133_) == 4)
{
lean_object* v_declName_5134_; 
v_declName_5134_ = lean_ctor_get(v___x_5133_, 0);
lean_inc(v_declName_5134_);
lean_dec_ref_known(v___x_5133_, 2);
if (lean_obj_tag(v_declName_5134_) == 1)
{
lean_object* v_pre_5135_; 
v_pre_5135_ = lean_ctor_get(v_declName_5134_, 0);
lean_inc(v_pre_5135_);
if (lean_obj_tag(v_pre_5135_) == 1)
{
lean_object* v_pre_5136_; 
v_pre_5136_ = lean_ctor_get(v_pre_5135_, 0);
switch(lean_obj_tag(v_pre_5136_))
{
case 1:
{
lean_object* v_pre_5137_; 
lean_inc_ref(v_pre_5136_);
lean_del_object(v___x_5131_);
v_pre_5137_ = lean_ctor_get(v_pre_5136_, 0);
if (lean_obj_tag(v_pre_5137_) == 0)
{
lean_object* v_str_5138_; lean_object* v_str_5139_; lean_object* v_str_5140_; lean_object* v___x_5141_; uint8_t v___x_5142_; 
v_str_5138_ = lean_ctor_get(v_declName_5134_, 1);
lean_inc_ref(v_str_5138_);
lean_dec_ref_known(v_declName_5134_, 2);
v_str_5139_ = lean_ctor_get(v_pre_5135_, 1);
lean_inc_ref(v_str_5139_);
lean_dec_ref_known(v_pre_5135_, 2);
v_str_5140_ = lean_ctor_get(v_pre_5136_, 1);
lean_inc_ref(v_str_5140_);
lean_dec_ref_known(v_pre_5136_, 2);
v___x_5141_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5142_ = lean_string_dec_eq(v_str_5140_, v___x_5141_);
lean_dec_ref(v_str_5140_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; 
lean_dec_ref(v_str_5139_);
lean_dec_ref(v_str_5138_);
v___x_5143_ = lean_box(0);
return v___x_5143_;
}
else
{
lean_object* v___x_5144_; uint8_t v___x_5145_; 
v___x_5144_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5145_ = lean_string_dec_eq(v_str_5139_, v___x_5144_);
lean_dec_ref(v_str_5139_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; 
lean_dec_ref(v_str_5138_);
v___x_5146_ = lean_box(0);
return v___x_5146_;
}
else
{
uint8_t v___x_5147_; 
v___x_5147_ = lean_string_dec_eq(v_str_5138_, v___x_5144_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; uint8_t v___x_5149_; 
v___x_5148_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5149_ = lean_string_dec_eq(v_str_5138_, v___x_5148_);
lean_dec_ref(v_str_5138_);
if (v___x_5149_ == 0)
{
lean_object* v___x_5150_; 
v___x_5150_ = lean_box(0);
return v___x_5150_;
}
else
{
lean_object* v___x_5151_; 
v___x_5151_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5151_;
}
}
else
{
lean_object* v___x_5152_; 
lean_dec_ref(v_str_5138_);
v___x_5152_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5152_;
}
}
}
}
else
{
lean_object* v___x_5153_; 
lean_dec_ref_known(v_pre_5136_, 2);
lean_dec_ref_known(v_pre_5135_, 2);
lean_dec_ref_known(v_declName_5134_, 2);
v___x_5153_ = lean_box(0);
return v___x_5153_;
}
}
case 0:
{
lean_object* v_str_5154_; lean_object* v_str_5155_; lean_object* v___x_5156_; uint8_t v___x_5157_; 
v_str_5154_ = lean_ctor_get(v_declName_5134_, 1);
lean_inc_ref(v_str_5154_);
lean_dec_ref_known(v_declName_5134_, 2);
v_str_5155_ = lean_ctor_get(v_pre_5135_, 1);
lean_inc_ref(v_str_5155_);
lean_dec_ref_known(v_pre_5135_, 2);
v___x_5156_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5157_ = lean_string_dec_eq(v_str_5155_, v___x_5156_);
lean_dec_ref(v_str_5155_);
if (v___x_5157_ == 0)
{
lean_object* v___x_5158_; 
lean_dec_ref(v_str_5154_);
lean_del_object(v___x_5131_);
v___x_5158_ = lean_box(0);
return v___x_5158_;
}
else
{
lean_object* v___x_5159_; uint8_t v___x_5160_; 
v___x_5159_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5160_ = lean_string_dec_eq(v_str_5154_, v___x_5159_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5161_; uint8_t v___x_5162_; 
v___x_5161_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5162_ = lean_string_dec_eq(v_str_5154_, v___x_5161_);
lean_dec_ref(v_str_5154_);
if (v___x_5162_ == 0)
{
lean_object* v___x_5163_; 
lean_del_object(v___x_5131_);
v___x_5163_ = lean_box(0);
return v___x_5163_;
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5166_; 
v___x_5164_ = lean_box(v___x_5157_);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 0, v___x_5164_);
v___x_5166_ = v___x_5131_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
else
{
lean_object* v___x_5168_; lean_object* v___x_5170_; 
lean_dec_ref(v_str_5154_);
v___x_5168_ = lean_box(v___x_5157_);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 0, v___x_5168_);
v___x_5170_ = v___x_5131_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5168_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
}
default: 
{
lean_object* v___x_5172_; 
lean_dec_ref_known(v_pre_5135_, 2);
lean_dec_ref_known(v_declName_5134_, 2);
lean_del_object(v___x_5131_);
v___x_5172_ = lean_box(0);
return v___x_5172_;
}
}
}
else
{
lean_object* v___x_5173_; 
lean_dec_ref_known(v_declName_5134_, 2);
lean_dec(v_pre_5135_);
lean_del_object(v___x_5131_);
v___x_5173_ = lean_box(0);
return v___x_5173_;
}
}
else
{
lean_object* v___x_5174_; 
lean_dec(v_declName_5134_);
lean_del_object(v___x_5131_);
v___x_5174_ = lean_box(0);
return v___x_5174_;
}
}
else
{
lean_object* v___x_5175_; 
lean_dec_ref(v___x_5133_);
lean_del_object(v___x_5131_);
v___x_5175_ = lean_box(0);
return v___x_5175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_){
_start:
{
if (lean_obj_tag(v_a_5178_) == 0)
{
lean_object* v___x_5180_; 
lean_dec_ref(v_env_5177_);
v___x_5180_ = lean_array_to_list(v_a_5179_);
return v___x_5180_;
}
else
{
lean_object* v_head_5181_; lean_object* v_snd_5182_; 
v_head_5181_ = lean_ctor_get(v_a_5178_, 0);
v_snd_5182_ = lean_ctor_get(v_head_5181_, 1);
if (lean_obj_tag(v_snd_5182_) == 0)
{
lean_object* v_tail_5183_; lean_object* v_fst_5184_; lean_object* v___x_5185_; 
lean_inc(v_head_5181_);
v_tail_5183_ = lean_ctor_get(v_a_5178_, 1);
lean_inc(v_tail_5183_);
lean_dec_ref_known(v_a_5178_, 2);
v_fst_5184_ = lean_ctor_get(v_head_5181_, 0);
lean_inc_n(v_fst_5184_, 2);
lean_dec(v_head_5181_);
lean_inc_ref(v_env_5177_);
v___x_5185_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5177_, v_fst_5184_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_dec(v_fst_5184_);
v_a_5178_ = v_tail_5183_;
goto _start;
}
else
{
lean_object* v_val_5187_; lean_object* v___x_5188_; uint8_t v___x_5189_; lean_object* v___x_5190_; 
v_val_5187_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_val_5187_);
lean_dec_ref_known(v___x_5185_, 1);
v___x_5188_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5188_, 0, v_fst_5184_);
v___x_5189_ = lean_unbox(v_val_5187_);
lean_dec(v_val_5187_);
lean_ctor_set_uint8(v___x_5188_, sizeof(void*)*1, v___x_5189_);
v___x_5190_ = lean_array_push(v_a_5179_, v___x_5188_);
v_a_5178_ = v_tail_5183_;
v_a_5179_ = v___x_5190_;
goto _start;
}
}
else
{
lean_object* v_tail_5192_; 
v_tail_5192_ = lean_ctor_get(v_a_5178_, 1);
lean_inc(v_tail_5192_);
lean_dec_ref_known(v_a_5178_, 2);
v_a_5178_ = v_tail_5192_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5197_, lean_object* v_as_x27_5198_, lean_object* v_b_5199_){
_start:
{
if (lean_obj_tag(v_as_x27_5198_) == 0)
{
lean_dec_ref(v_env_5197_);
lean_inc_ref(v_b_5199_);
return v_b_5199_;
}
else
{
lean_object* v_head_5200_; lean_object* v_tail_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; 
v_head_5200_ = lean_ctor_get(v_as_x27_5198_, 0);
v_tail_5201_ = lean_ctor_get(v_as_x27_5198_, 1);
v___x_5202_ = lean_box(0);
v___x_5203_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5200_) == 1)
{
lean_object* v_fields_5204_; 
v_fields_5204_ = lean_ctor_get(v_head_5200_, 1);
if (lean_obj_tag(v_fields_5204_) == 0)
{
lean_object* v_n_5205_; lean_object* v___x_5206_; 
v_n_5205_ = lean_ctor_get(v_head_5200_, 0);
lean_inc(v_n_5205_);
lean_inc_ref(v_env_5197_);
v___x_5206_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5197_, v_n_5205_);
if (lean_obj_tag(v___x_5206_) == 1)
{
lean_object* v_val_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5219_; 
lean_dec_ref(v_env_5197_);
v_val_5207_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5209_ = v___x_5206_;
v_isShared_5210_ = v_isSharedCheck_5219_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_val_5207_);
lean_dec(v___x_5206_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5219_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5216_; 
lean_inc(v_n_5205_);
v___x_5211_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5211_, 0, v_n_5205_);
v___x_5212_ = lean_unbox(v_val_5207_);
lean_dec(v_val_5207_);
lean_ctor_set_uint8(v___x_5211_, sizeof(void*)*1, v___x_5212_);
v___x_5213_ = lean_box(0);
v___x_5214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5214_, 0, v___x_5211_);
lean_ctor_set(v___x_5214_, 1, v___x_5213_);
if (v_isShared_5210_ == 0)
{
lean_ctor_set(v___x_5209_, 0, v___x_5214_);
v___x_5216_ = v___x_5209_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5214_);
v___x_5216_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
lean_object* v___x_5217_; 
v___x_5217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5216_);
lean_ctor_set(v___x_5217_, 1, v___x_5202_);
return v___x_5217_;
}
}
}
else
{
lean_dec(v___x_5206_);
v_as_x27_5198_ = v_tail_5201_;
v_b_5199_ = v___x_5203_;
goto _start;
}
}
else
{
v_as_x27_5198_ = v_tail_5201_;
v_b_5199_ = v___x_5203_;
goto _start;
}
}
else
{
v_as_x27_5198_ = v_tail_5201_;
v_b_5199_ = v___x_5203_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5223_, lean_object* v_as_x27_5224_, lean_object* v_b_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5223_, v_as_x27_5224_, v_b_5225_);
lean_dec_ref(v_b_5225_);
lean_dec(v_as_x27_5224_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5229_, lean_object* v_opts_5230_, lean_object* v_currNamespace_5231_, lean_object* v_openDecls_5232_, lean_object* v_ident_5233_){
_start:
{
if (lean_obj_tag(v_ident_5233_) == 3)
{
lean_object* v_val_5234_; lean_object* v_preresolved_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v_fst_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5273_; 
v_val_5234_ = lean_ctor_get(v_ident_5233_, 2);
lean_inc(v_val_5234_);
v_preresolved_5235_ = lean_ctor_get(v_ident_5233_, 3);
lean_inc(v_preresolved_5235_);
lean_dec_ref_known(v_ident_5233_, 4);
v___x_5236_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5229_);
v___x_5237_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5229_, v_preresolved_5235_, v___x_5236_);
lean_dec(v_preresolved_5235_);
v_fst_5238_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5273_ == 0)
{
lean_object* v_unused_5274_; 
v_unused_5274_ = lean_ctor_get(v___x_5237_, 1);
lean_dec(v_unused_5274_);
v___x_5240_ = v___x_5237_;
v_isShared_5241_ = v_isSharedCheck_5273_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_fst_5238_);
lean_dec(v___x_5237_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5273_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
if (lean_obj_tag(v_fst_5238_) == 0)
{
lean_object* v___x_5242_; uint8_t v___x_5243_; 
v___x_5242_ = l_Lean_Name_eraseMacroScopes(v_val_5234_);
lean_inc_ref(v_env_5229_);
v___x_5243_ = l_Lean_Parser_isParserCategory(v_env_5229_, v___x_5242_);
if (v___x_5243_ == 0)
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; 
lean_inc_ref_n(v_env_5229_, 2);
v___x_5244_ = l_Lean_ResolveName_resolveGlobalName(v_env_5229_, v_opts_5230_, v_currNamespace_5231_, v_openDecls_5232_, v_val_5234_);
v___x_5245_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5246_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5229_, v___x_5244_, v___x_5245_);
v___x_5247_ = l_List_isEmpty___redArg(v___x_5246_);
if (v___x_5247_ == 0)
{
lean_dec(v___x_5242_);
lean_del_object(v___x_5240_);
lean_dec_ref(v_env_5229_);
return v___x_5246_;
}
else
{
lean_object* v___x_5248_; lean_object* v_asyncMode_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; 
lean_dec(v___x_5246_);
v___x_5248_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5249_ = lean_ctor_get(v___x_5248_, 2);
v___x_5250_ = lean_box(1);
v___x_5251_ = lean_box(0);
v___x_5252_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5250_, v___x_5248_, v_env_5229_, v_asyncMode_5249_, v___x_5251_);
v___x_5253_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5252_, v___x_5242_);
lean_dec(v___x_5242_);
lean_dec(v___x_5252_);
if (lean_obj_tag(v___x_5253_) == 1)
{
lean_object* v_val_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5265_; 
v_val_5254_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5256_ = v___x_5253_;
v_isShared_5257_ = v_isSharedCheck_5265_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_val_5254_);
lean_dec(v___x_5253_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5265_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
lean_ctor_set_tag(v___x_5256_, 2);
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_val_5254_);
v___x_5259_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
lean_object* v___x_5260_; lean_object* v___x_5262_; 
v___x_5260_ = lean_box(0);
if (v_isShared_5241_ == 0)
{
lean_ctor_set_tag(v___x_5240_, 1);
lean_ctor_set(v___x_5240_, 1, v___x_5260_);
lean_ctor_set(v___x_5240_, 0, v___x_5259_);
v___x_5262_ = v___x_5240_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5259_);
lean_ctor_set(v_reuseFailAlloc_5263_, 1, v___x_5260_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
else
{
lean_object* v___x_5266_; 
lean_dec(v___x_5253_);
lean_del_object(v___x_5240_);
v___x_5266_ = lean_box(0);
return v___x_5266_;
}
}
}
else
{
lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5270_; 
lean_dec(v_val_5234_);
lean_dec(v_openDecls_5232_);
lean_dec(v_currNamespace_5231_);
lean_dec_ref(v_env_5229_);
v___x_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5267_, 0, v___x_5242_);
v___x_5268_ = lean_box(0);
if (v_isShared_5241_ == 0)
{
lean_ctor_set_tag(v___x_5240_, 1);
lean_ctor_set(v___x_5240_, 1, v___x_5268_);
lean_ctor_set(v___x_5240_, 0, v___x_5267_);
v___x_5270_ = v___x_5240_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v___x_5267_);
lean_ctor_set(v_reuseFailAlloc_5271_, 1, v___x_5268_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
return v___x_5270_;
}
}
}
else
{
lean_object* v_val_5272_; 
lean_del_object(v___x_5240_);
lean_dec(v_val_5234_);
lean_dec(v_openDecls_5232_);
lean_dec(v_currNamespace_5231_);
lean_dec_ref(v_env_5229_);
v_val_5272_ = lean_ctor_get(v_fst_5238_, 0);
lean_inc(v_val_5272_);
lean_dec_ref_known(v_fst_5238_, 1);
return v_val_5272_;
}
}
}
else
{
lean_object* v___x_5275_; 
lean_dec(v_ident_5233_);
lean_dec(v_openDecls_5232_);
lean_dec(v_currNamespace_5231_);
lean_dec_ref(v_env_5229_);
v___x_5275_ = lean_box(0);
return v___x_5275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5276_, lean_object* v_opts_5277_, lean_object* v_currNamespace_5278_, lean_object* v_openDecls_5279_, lean_object* v_ident_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5276_, v_opts_5277_, v_currNamespace_5278_, v_openDecls_5279_, v_ident_5280_);
lean_dec_ref(v_opts_5277_);
return v_res_5281_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5282_, lean_object* v_as_5283_, lean_object* v_as_x27_5284_, lean_object* v_b_5285_, lean_object* v_a_5286_){
_start:
{
lean_object* v___x_5287_; 
v___x_5287_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5282_, v_as_x27_5284_, v_b_5285_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5288_, lean_object* v_as_5289_, lean_object* v_as_x27_5290_, lean_object* v_b_5291_, lean_object* v_a_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5288_, v_as_5289_, v_as_x27_5290_, v_b_5291_, v_a_5292_);
lean_dec_ref(v_b_5291_);
lean_dec(v_as_x27_5290_);
lean_dec(v_as_5289_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5294_, lean_object* v_id_5295_, uint8_t v_unsetExporting_5296_){
_start:
{
lean_object* v___y_5298_; 
if (v_unsetExporting_5296_ == 0)
{
lean_object* v_toParserModuleContext_5304_; lean_object* v_env_5305_; 
v_toParserModuleContext_5304_ = lean_ctor_get(v_ctx_5294_, 1);
v_env_5305_ = lean_ctor_get(v_toParserModuleContext_5304_, 0);
lean_inc_ref(v_env_5305_);
v___y_5298_ = v_env_5305_;
goto v___jp_5297_;
}
else
{
lean_object* v_toParserModuleContext_5306_; lean_object* v_env_5307_; uint8_t v___x_5308_; lean_object* v___x_5309_; 
v_toParserModuleContext_5306_ = lean_ctor_get(v_ctx_5294_, 1);
v_env_5307_ = lean_ctor_get(v_toParserModuleContext_5306_, 0);
v___x_5308_ = 0;
lean_inc_ref(v_env_5307_);
v___x_5309_ = l_Lean_Environment_setExporting(v_env_5307_, v___x_5308_);
v___y_5298_ = v___x_5309_;
goto v___jp_5297_;
}
v___jp_5297_:
{
lean_object* v_toParserModuleContext_5299_; lean_object* v_options_5300_; lean_object* v_currNamespace_5301_; lean_object* v_openDecls_5302_; lean_object* v___x_5303_; 
v_toParserModuleContext_5299_ = lean_ctor_get(v_ctx_5294_, 1);
lean_inc_ref(v_toParserModuleContext_5299_);
lean_dec_ref(v_ctx_5294_);
v_options_5300_ = lean_ctor_get(v_toParserModuleContext_5299_, 1);
lean_inc_ref(v_options_5300_);
v_currNamespace_5301_ = lean_ctor_get(v_toParserModuleContext_5299_, 2);
lean_inc(v_currNamespace_5301_);
v_openDecls_5302_ = lean_ctor_get(v_toParserModuleContext_5299_, 3);
lean_inc(v_openDecls_5302_);
lean_dec_ref(v_toParserModuleContext_5299_);
v___x_5303_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5298_, v_options_5300_, v_currNamespace_5301_, v_openDecls_5302_, v_id_5295_);
lean_dec_ref(v_options_5300_);
return v___x_5303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5310_, lean_object* v_id_5311_, lean_object* v_unsetExporting_5312_){
_start:
{
uint8_t v_unsetExporting_boxed_5313_; lean_object* v_res_5314_; 
v_unsetExporting_boxed_5313_ = lean_unbox(v_unsetExporting_5312_);
v_res_5314_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5310_, v_id_5311_, v_unsetExporting_boxed_5313_);
return v_res_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_){
_start:
{
lean_object* v___x_5319_; lean_object* v_env_5320_; lean_object* v_options_5321_; lean_object* v_currNamespace_5322_; lean_object* v_openDecls_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5319_ = lean_st_ref_get(v_a_5317_);
v_env_5320_ = lean_ctor_get(v___x_5319_, 0);
lean_inc_ref(v_env_5320_);
lean_dec(v___x_5319_);
v_options_5321_ = lean_ctor_get(v_a_5316_, 2);
v_currNamespace_5322_ = lean_ctor_get(v_a_5316_, 6);
v_openDecls_5323_ = lean_ctor_get(v_a_5316_, 7);
lean_inc(v_openDecls_5323_);
lean_inc(v_currNamespace_5322_);
v___x_5324_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5320_, v_options_5321_, v_currNamespace_5322_, v_openDecls_5323_, v_id_5315_);
v___x_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5325_, 0, v___x_5324_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Lean_Parser_resolveParserName(v_id_5326_, v_a_5327_, v_a_5328_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
return v_res_5330_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5331_, lean_object* v_x_5332_){
_start:
{
if (lean_obj_tag(v_x_5331_) == 0)
{
if (lean_obj_tag(v_x_5332_) == 0)
{
uint8_t v___x_5333_; 
v___x_5333_ = 1;
return v___x_5333_;
}
else
{
uint8_t v___x_5334_; 
v___x_5334_ = 0;
return v___x_5334_;
}
}
else
{
if (lean_obj_tag(v_x_5332_) == 0)
{
uint8_t v___x_5335_; 
v___x_5335_ = 0;
return v___x_5335_;
}
else
{
lean_object* v_val_5336_; lean_object* v_val_5337_; uint8_t v___x_5338_; 
v_val_5336_ = lean_ctor_get(v_x_5331_, 0);
v_val_5337_ = lean_ctor_get(v_x_5332_, 0);
v___x_5338_ = l_Lean_Parser_instBEqError_beq(v_val_5336_, v_val_5337_);
return v___x_5338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5339_, lean_object* v_x_5340_){
_start:
{
uint8_t v_res_5341_; lean_object* v_r_5342_; 
v_res_5341_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5339_, v_x_5340_);
lean_dec(v_x_5340_);
lean_dec(v_x_5339_);
v_r_5342_ = lean_box(v_res_5341_);
return v_r_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5343_, lean_object* v_ctx_5344_){
_start:
{
lean_object* v_toParserModuleContext_5345_; lean_object* v_toInputContext_5346_; lean_object* v_toCacheableParserContext_5347_; lean_object* v_tokens_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5373_; 
v_toParserModuleContext_5345_ = lean_ctor_get(v_ctx_5344_, 1);
v_toInputContext_5346_ = lean_ctor_get(v_ctx_5344_, 0);
v_toCacheableParserContext_5347_ = lean_ctor_get(v_ctx_5344_, 2);
v_tokens_5348_ = lean_ctor_get(v_ctx_5344_, 3);
v_isSharedCheck_5373_ = !lean_is_exclusive(v_ctx_5344_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5350_ = v_ctx_5344_;
v_isShared_5351_ = v_isSharedCheck_5373_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_tokens_5348_);
lean_inc(v_toCacheableParserContext_5347_);
lean_inc(v_toParserModuleContext_5345_);
lean_inc(v_toInputContext_5346_);
lean_dec(v_ctx_5344_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5373_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v_env_5352_; lean_object* v_options_5353_; lean_object* v_currNamespace_5354_; lean_object* v_openDecls_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5372_; 
v_env_5352_ = lean_ctor_get(v_toParserModuleContext_5345_, 0);
v_options_5353_ = lean_ctor_get(v_toParserModuleContext_5345_, 1);
v_currNamespace_5354_ = lean_ctor_get(v_toParserModuleContext_5345_, 2);
v_openDecls_5355_ = lean_ctor_get(v_toParserModuleContext_5345_, 3);
v_isSharedCheck_5372_ = !lean_is_exclusive(v_toParserModuleContext_5345_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5357_ = v_toParserModuleContext_5345_;
v_isShared_5358_ = v_isSharedCheck_5372_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_openDecls_5355_);
lean_inc(v_currNamespace_5354_);
lean_inc(v_options_5353_);
lean_inc(v_env_5352_);
lean_dec(v_toParserModuleContext_5345_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5372_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; uint8_t v___y_5361_; lean_object* v___x_5369_; uint8_t v___x_5370_; 
v___x_5359_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5369_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5370_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5353_, v___x_5369_);
if (v___x_5370_ == 0)
{
uint8_t v___x_5371_; 
v___x_5371_ = 1;
v___y_5361_ = v___x_5371_;
goto v___jp_5360_;
}
else
{
v___y_5361_ = v___x_5343_;
goto v___jp_5360_;
}
v___jp_5360_:
{
lean_object* v___x_5362_; lean_object* v___x_5364_; 
v___x_5362_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5353_, v___x_5359_, v___y_5361_);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v___x_5362_);
v___x_5364_ = v___x_5357_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_env_5352_);
lean_ctor_set(v_reuseFailAlloc_5368_, 1, v___x_5362_);
lean_ctor_set(v_reuseFailAlloc_5368_, 2, v_currNamespace_5354_);
lean_ctor_set(v_reuseFailAlloc_5368_, 3, v_openDecls_5355_);
v___x_5364_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
lean_object* v___x_5366_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 1, v___x_5364_);
v___x_5366_ = v___x_5350_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_toInputContext_5346_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v___x_5364_);
lean_ctor_set(v_reuseFailAlloc_5367_, 2, v_toCacheableParserContext_5347_);
lean_ctor_set(v_reuseFailAlloc_5367_, 3, v_tokens_5348_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5374_, lean_object* v_ctx_5375_){
_start:
{
uint8_t v___x_1088__boxed_5376_; lean_object* v_res_5377_; 
v___x_1088__boxed_5376_ = lean_unbox(v___x_5374_);
v_res_5377_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1088__boxed_5376_, v_ctx_5375_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5385_, lean_object* v_ctx_5386_, lean_object* v_s_5387_){
_start:
{
lean_object* v_stxStack_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; uint8_t v___x_5392_; 
v_stxStack_5388_ = lean_ctor_get(v_s_5387_, 0);
v___x_5389_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5388_);
v___x_5390_ = lean_unsigned_to_nat(1u);
v___x_5391_ = lean_nat_add(v_offset_5385_, v___x_5390_);
v___x_5392_ = lean_nat_dec_lt(v___x_5389_, v___x_5391_);
lean_dec(v___x_5391_);
if (v___x_5392_ == 0)
{
lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5393_ = lean_nat_sub(v___x_5389_, v_offset_5385_);
lean_dec(v___x_5389_);
v___x_5394_ = lean_nat_sub(v___x_5393_, v___x_5390_);
lean_dec(v___x_5393_);
v___x_5395_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5388_, v___x_5394_);
lean_dec(v___x_5394_);
if (lean_obj_tag(v___x_5395_) == 3)
{
uint8_t v___x_5407_; lean_object* v___x_5408_; 
v___x_5407_ = 1;
lean_inc_ref(v___x_5395_);
lean_inc_ref(v_ctx_5386_);
v___x_5408_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5386_, v___x_5395_, v___x_5407_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
lean_dec_ref(v_ctx_5386_);
v___x_5409_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5410_ = lean_box(0);
v___x_5411_ = l_Lean_Syntax_formatStx(v___x_5395_, v___x_5410_, v___x_5392_);
v___x_5412_ = l_Std_Format_defWidth;
v___x_5413_ = lean_unsigned_to_nat(0u);
v___x_5414_ = l_Std_Format_pretty(v___x_5411_, v___x_5412_, v___x_5413_, v___x_5413_);
v___x_5415_ = lean_string_append(v___x_5409_, v___x_5414_);
lean_dec_ref(v___x_5414_);
v___x_5416_ = lean_box(0);
v___x_5417_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5387_, v___x_5415_, v___x_5416_, v___x_5407_);
return v___x_5417_;
}
else
{
lean_object* v_head_5418_; lean_object* v_tail_5419_; lean_object* v_iniSz_5420_; lean_object* v_s_5422_; 
v_head_5418_ = lean_ctor_get(v___x_5408_, 0);
lean_inc(v_head_5418_);
v_tail_5419_ = lean_ctor_get(v___x_5408_, 1);
lean_inc(v_tail_5419_);
lean_dec_ref_known(v___x_5408_, 2);
v_iniSz_5420_ = l_Lean_Parser_ParserState_stackSize(v_s_5387_);
switch(lean_obj_tag(v_head_5418_))
{
case 0:
{
if (lean_obj_tag(v_tail_5419_) == 0)
{
lean_object* v_cat_5432_; lean_object* v___x_5433_; 
lean_dec_ref_known(v___x_5395_, 4);
v_cat_5432_ = lean_ctor_get(v_head_5418_, 0);
lean_inc(v_cat_5432_);
lean_dec_ref_known(v_head_5418_, 1);
v___x_5433_ = l_Lean_Parser_categoryParserFn(v_cat_5432_, v_ctx_5386_, v_s_5387_);
v_s_5422_ = v___x_5433_;
goto v___jp_5421_;
}
else
{
lean_dec_ref_known(v_tail_5419_, 2);
lean_dec_ref_known(v_head_5418_, 1);
lean_dec(v_iniSz_5420_);
lean_dec_ref(v_ctx_5386_);
goto v___jp_5396_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5419_) == 0)
{
lean_object* v_decl_5434_; lean_object* v___x_5435_; lean_object* v___f_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
lean_dec_ref_known(v___x_5395_, 4);
v_decl_5434_ = lean_ctor_get(v_head_5418_, 0);
lean_inc(v_decl_5434_);
lean_dec_ref_known(v_head_5418_, 1);
v___x_5435_ = lean_box(v___x_5392_);
v___f_5436_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5436_, 0, v___x_5435_);
v___x_5437_ = lean_box(0);
v___x_5438_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5438_, 0, v_decl_5434_);
lean_closure_set(v___x_5438_, 1, v___x_5437_);
v___x_5439_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5436_, v___x_5438_, v_ctx_5386_, v_s_5387_);
v_s_5422_ = v___x_5439_;
goto v___jp_5421_;
}
else
{
lean_dec_ref_known(v_tail_5419_, 2);
lean_dec_ref_known(v_head_5418_, 1);
lean_dec(v_iniSz_5420_);
lean_dec_ref(v_ctx_5386_);
goto v___jp_5396_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5419_) == 0)
{
lean_object* v_p_5440_; 
v_p_5440_ = lean_ctor_get(v_head_5418_, 0);
lean_inc_ref(v_p_5440_);
lean_dec_ref_known(v_head_5418_, 1);
if (lean_obj_tag(v_p_5440_) == 0)
{
lean_object* v_p_5441_; lean_object* v_fn_5442_; lean_object* v___x_5443_; 
lean_dec_ref_known(v___x_5395_, 4);
v_p_5441_ = lean_ctor_get(v_p_5440_, 0);
lean_inc(v_p_5441_);
lean_dec_ref_known(v_p_5440_, 1);
v_fn_5442_ = lean_ctor_get(v_p_5441_, 1);
lean_inc_ref(v_fn_5442_);
lean_dec(v_p_5441_);
v___x_5443_ = lean_apply_2(v_fn_5442_, v_ctx_5386_, v_s_5387_);
v_s_5422_ = v___x_5443_;
goto v___jp_5421_;
}
else
{
lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; 
lean_dec_ref(v_p_5440_);
lean_dec(v_iniSz_5420_);
lean_dec_ref(v_ctx_5386_);
v___x_5444_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5445_ = lean_box(0);
v___x_5446_ = l_Lean_Syntax_formatStx(v___x_5395_, v___x_5445_, v___x_5392_);
v___x_5447_ = l_Std_Format_defWidth;
v___x_5448_ = lean_unsigned_to_nat(0u);
v___x_5449_ = l_Std_Format_pretty(v___x_5446_, v___x_5447_, v___x_5448_, v___x_5448_);
v___x_5450_ = lean_string_append(v___x_5444_, v___x_5449_);
lean_dec_ref(v___x_5449_);
v___x_5451_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5452_ = lean_string_append(v___x_5450_, v___x_5451_);
v___x_5453_ = lean_box(0);
v___x_5454_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5387_, v___x_5452_, v___x_5453_, v___x_5407_);
return v___x_5454_;
}
}
else
{
lean_dec_ref_known(v_tail_5419_, 2);
lean_dec_ref_known(v_head_5418_, 1);
lean_dec(v_iniSz_5420_);
lean_dec_ref(v_ctx_5386_);
goto v___jp_5396_;
}
}
}
v___jp_5421_:
{
lean_object* v_errorMsg_5423_; lean_object* v___x_5424_; uint8_t v___x_5425_; 
v_errorMsg_5423_ = lean_ctor_get(v_s_5422_, 4);
v___x_5424_ = lean_box(0);
v___x_5425_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5423_, v___x_5424_);
if (v___x_5425_ == 0)
{
lean_dec(v_iniSz_5420_);
return v_s_5422_;
}
else
{
lean_object* v___x_5426_; lean_object* v___x_5427_; uint8_t v___x_5428_; 
v___x_5426_ = l_Lean_Parser_ParserState_stackSize(v_s_5422_);
v___x_5427_ = lean_nat_add(v_iniSz_5420_, v___x_5390_);
lean_dec(v_iniSz_5420_);
v___x_5428_ = lean_nat_dec_eq(v___x_5426_, v___x_5427_);
lean_dec(v___x_5427_);
lean_dec(v___x_5426_);
if (v___x_5428_ == 0)
{
lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5429_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5430_ = lean_box(0);
v___x_5431_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5422_, v___x_5429_, v___x_5430_, v___x_5425_);
return v___x_5431_;
}
else
{
return v_s_5422_;
}
}
}
}
}
else
{
lean_object* v___x_5455_; lean_object* v___x_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; 
lean_dec(v___x_5395_);
lean_dec_ref(v_ctx_5386_);
v___x_5455_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5456_ = lean_box(0);
v___x_5457_ = 1;
v___x_5458_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5387_, v___x_5455_, v___x_5456_, v___x_5457_);
return v___x_5458_;
}
v___jp_5396_:
{
lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; uint8_t v___x_5405_; lean_object* v___x_5406_; 
v___x_5397_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5398_ = lean_box(0);
v___x_5399_ = l_Lean_Syntax_formatStx(v___x_5395_, v___x_5398_, v___x_5392_);
v___x_5400_ = l_Std_Format_defWidth;
v___x_5401_ = lean_unsigned_to_nat(0u);
v___x_5402_ = l_Std_Format_pretty(v___x_5399_, v___x_5400_, v___x_5401_, v___x_5401_);
v___x_5403_ = lean_string_append(v___x_5397_, v___x_5402_);
lean_dec_ref(v___x_5402_);
v___x_5404_ = lean_box(0);
v___x_5405_ = 1;
v___x_5406_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5387_, v___x_5403_, v___x_5404_, v___x_5405_);
return v___x_5406_;
}
}
else
{
lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
lean_dec(v___x_5389_);
lean_dec_ref(v_ctx_5386_);
v___x_5459_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5460_ = lean_box(0);
v___x_5461_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5387_, v___x_5459_, v___x_5460_, v___x_5392_);
return v___x_5461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5462_, lean_object* v_ctx_5463_, lean_object* v_s_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l_Lean_Parser_parserOfStackFn(v_offset_5462_, v_ctx_5463_, v_s_5464_);
lean_dec(v_offset_5462_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5466_, lean_object* v_x_5467_){
_start:
{
lean_object* v_quotDepth_5468_; uint8_t v_suppressInsideQuot_5469_; lean_object* v_savedPos_x3f_5470_; lean_object* v_forbiddenTks_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5478_; 
v_quotDepth_5468_ = lean_ctor_get(v_x_5467_, 1);
v_suppressInsideQuot_5469_ = lean_ctor_get_uint8(v_x_5467_, sizeof(void*)*4);
v_savedPos_x3f_5470_ = lean_ctor_get(v_x_5467_, 2);
v_forbiddenTks_5471_ = lean_ctor_get(v_x_5467_, 3);
v_isSharedCheck_5478_ = !lean_is_exclusive(v_x_5467_);
if (v_isSharedCheck_5478_ == 0)
{
lean_object* v_unused_5479_; 
v_unused_5479_ = lean_ctor_get(v_x_5467_, 0);
lean_dec(v_unused_5479_);
v___x_5473_ = v_x_5467_;
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_forbiddenTks_5471_);
lean_inc(v_savedPos_x3f_5470_);
lean_inc(v_quotDepth_5468_);
lean_dec(v_x_5467_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___x_5476_; 
if (v_isShared_5474_ == 0)
{
lean_ctor_set(v___x_5473_, 0, v_prec_5466_);
v___x_5476_ = v___x_5473_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_prec_5466_);
lean_ctor_set(v_reuseFailAlloc_5477_, 1, v_quotDepth_5468_);
lean_ctor_set(v_reuseFailAlloc_5477_, 2, v_savedPos_x3f_5470_);
lean_ctor_set(v_reuseFailAlloc_5477_, 3, v_forbiddenTks_5471_);
lean_ctor_set_uint8(v_reuseFailAlloc_5477_, sizeof(void*)*4, v_suppressInsideQuot_5469_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5480_){
_start:
{
lean_inc(v___y_5480_);
return v___y_5480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5481_);
lean_dec(v___y_5481_);
return v_res_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5483_){
_start:
{
lean_inc_ref(v___y_5483_);
return v___y_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5484_){
_start:
{
lean_object* v_res_5485_; 
v_res_5485_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5484_);
lean_dec_ref(v___y_5484_);
return v_res_5485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5492_, lean_object* v_prec_5493_){
_start:
{
lean_object* v___f_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___f_5494_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5494_, 0, v_prec_5493_);
v___x_5495_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5496_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5496_, 0, v_offset_5492_);
v___x_5497_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5497_, 0, v___f_5494_);
lean_closure_set(v___x_5497_, 1, v___x_5496_);
v___x_5498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5498_, 0, v___x_5495_);
lean_ctor_set(v___x_5498_, 1, v___x_5497_);
return v___x_5498_;
}
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_BuiltinDocAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinTokenTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinTokenTable);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinSyntaxNodeKindSetRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinSyntaxNodeKindSetRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinParserCategoriesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinParserCategoriesRef);
lean_dec_ref(res);
l_Lean_Parser_ParserExtension_instInhabitedState_default = _init_l_Lean_Parser_ParserExtension_instInhabitedState_default();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState_default);
l_Lean_Parser_ParserExtension_instInhabitedState = _init_l_Lean_Parser_ParserExtension_instInhabitedState();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAliasesRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAlias2kindRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAlias2kindRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAliases2infoRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAliases2infoRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAttributeHooks = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAttributeHooks);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserExtension);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_internal_parseQuotWithCurrentStage = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_internal_parseQuotWithCurrentStage);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_aliasExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_aliasExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Extension(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_mkInputContext___auto__1 = _init_l_Lean_Parser_mkInputContext___auto__1();
lean_mark_persistent(l_Lean_Parser_mkInputContext___auto__1);
l_Lean_Parser_registerBuiltinParserAttribute___auto__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___auto__1);
l_Lean_Parser_mkParserAttributeImpl___auto__1 = _init_l_Lean_Parser_mkParserAttributeImpl___auto__1();
lean_mark_persistent(l_Lean_Parser_mkParserAttributeImpl___auto__1);
l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1 = _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1);
l_Lean_Parser_registerParserCategory___auto__1 = _init_l_Lean_Parser_registerParserCategory___auto__1();
lean_mark_persistent(l_Lean_Parser_registerParserCategory___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* initialize_Lean_BuiltinDocAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Extension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Extension(builtin);
}
#ifdef __cplusplus
}
#endif
